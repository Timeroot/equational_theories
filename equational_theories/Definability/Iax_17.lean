import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3566`: `x ◇ y = y ◇ ((z ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation3566 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3566 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3566.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op (M.op X2 X0) X1)) := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X3 (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op (M.op X2 X0) X1) X3 X1
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X1 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X0 X1 X2 X3
       have i₂ := eq8 X1 X3 X0
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq29 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq30 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op X0 X2)) ∨ (M.op X1 X0) = (k X1 X0) := by
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
  have eq31 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (M.op X2 X1) X0) ∨ (M.op (M.op X2 X1) X0) = (k (M.op X2 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 (M.op X2 X1) X2
       have i₂ := eq12 (M.op X2 X1) X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op (M.op X2 X0) X1)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 (M.op X2 X1) X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq35 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq46 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X1 X4) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq20 X0 X1 (M.op x x) X4
       have i₂ := eq20 x X0 x X1
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 (M.op x x)
       have i₂ := eq20 x X0 x X1
       grind)
    | exact superpose eq20 eq8
    | exact resolve eq8 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (k (M.op (M.op X1 X2) X0) (M.op X0 (M.op (M.op X1 X2) X0))) := by
    intro X0 X1 X2
    grind
  clear eq20
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (k (M.op (M.op X1 X2) X0) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X1 X2
       have i₂ := eq8 X2 X0 X1
       grind)
    | exact superpose eq8 eq53
    | exact resolve eq53 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq60 : ∀ X0 X2 : G, (M.op X2 X0) = (k (M.op X2 X0) (M.op X2 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq56 x X0 x
       have i₂ := eq46 X0 x x
       grind)
    | exact superpose eq46 eq56
    | exact resolve eq56 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq88 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq29 (τ X1) X0
       grind)
    | exact superpose eq29 eq17
    | (have j1 := eq29 (τ X1) X0
       grind)
    | exact resolve eq17 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq91 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq95 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq51 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq51
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq51 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) X2) = (M.op X2 (M.op (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq30 (σ X1) (σ X0) X2
       grind)
    | exact superpose eq30 eq13
    | (have j1 := eq30 (σ X1) (σ X0) X2
       grind)
    | exact resolve eq13 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq150 : ∀ X0 X1 X2 : G, (M.op (σ X0) X2) = (M.op (σ X1) X2) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq147 X0 X1 X2
       have i₂ := eq51 (σ X1) X2
       grind)
    | exact superpose eq51 eq147
    | (have j0 := eq147 X0 X1 X2
       grind)
    | exact resolve eq147 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq266 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq32 x y
       grind)
    | exact superpose eq32 eq14
    | (have j1 := eq32 x y
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 X1 X2 : G, (M.op (σ X1) X2) = (M.op (σ (k X0 X1)) X2) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46 (σ X0) (σ X1) X2
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq46
    | (have j1 := eq32 X0 X1
       grind)
    | exact resolve eq46 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq32 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq316 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq40
  have eq334 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq316 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq316
    | exact resolve eq316 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq356 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 X0)) ∨ (M.op X0 X1) = (k (M.op X2 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 x X1 X0
       have i₂ := eq46 X0 X1 x
       grind)
    | exact superpose eq46 eq31
    | exact resolve eq31 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq428 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X2 X0) X1) ∨ (M.op X0 X1) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq356 X0 X1 X2
       have i₂ := eq51 X2 X0
       grind)
    | exact superpose eq51 eq356
    | (have j0 := eq356 X0 X1 X2
       grind)
    | exact resolve eq356 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq551 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X0) ∨ (M.op X2 X0) = (k (M.op X2 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq91 (M.op X2 X0) X1
       have i₂ := eq46 X2 X0 X1
       grind)
    | exact superpose eq46 eq91
    | (have j0 := eq91 (M.op X2 X0) X1
       grind)
    | (have r₁ := eq91 (M.op x x) x
       have r₂ := eq46 x x x
       grind)
    | exact resolve eq91 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq849 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq60 X0 x
       have i₂ := eq12 X0 (M.op x X0)
       grind)
    | exact superpose eq12 eq60
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq60 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1146 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X0
       have i₂ := eq849 X0 X1
       grind)
    | exact superpose eq849 eq95
    | (have j0 := eq95 X0 X1
       have j1 := eq849 X0 X1
       grind)
    | exact resolve eq95 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq1169 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1146 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146
  have eq1529 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq35
    | exact resolve eq35 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1613 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1529 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1529
    | (have j0 := eq1529 X0 X1
       grind)
    | exact resolve eq1529 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529
  have eq1737 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq88
    | exact resolve eq88 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq1781 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1737 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1737
    | (have j0 := eq1737 X0 X1
       grind)
    | exact resolve eq1737 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1737
  have eq2759 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq266
       have i₂ := eq95 y x
       grind)
    | exact superpose eq95 eq266
    | (have j1 := eq95 y x
       grind)
    | exact resolve eq266 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq2760 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq266
       have i₂ := eq1169 y x
       grind)
    | exact superpose eq1169 eq266
    | (have j1 := eq1169 y x
       grind)
    | exact resolve eq266 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2761 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq266
       have i₂ := eq1781 y x
       grind)
    | exact superpose eq1781 eq266
    | (have j1 := eq1781 y x
       grind)
    | (have r₁ := eq266
       have r₂ := eq1781 y x
       grind)
    | exact resolve eq266 eq1781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1781
  have eq2762 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq266
       have i₂ := eq1613 y x
       grind)
    | exact superpose eq1613 eq266
    | (have j1 := eq1613 (σ y) (σ x)
       grind)
    | (have r₁ := eq266
       have r₂ := eq1613 y x
       grind)
    | exact resolve eq266 eq1613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq1613
  have eq2763 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2762
  have eq2764 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq2761
  have eq2765 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq2760
  have eq2766 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq2759
  have eq2781 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq334 x
       have i₂ := eq2763
       grind)
    | exact superpose eq2763 eq334
    | exact resolve eq334 eq2763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2763
  have eq2811 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2781
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2781
    | exact resolve eq2781 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2781
  have eq2903 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq2811
       grind)
    | exact superpose eq2811 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq2811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2811
  have eq2911 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq2903
  have eq3057 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq46 x y X0
       have i₂ := eq2911
       grind)
    | exact superpose eq2911 eq46
    | exact resolve eq46 eq2911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq5406 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq150 x y X0
       grind)
    | exact superpose eq150 eq14
    | (have j1 := eq150 x y X0
       grind)
    | exact resolve eq14 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq8893 : y = (k y (M.op x y)) ∨ y = (M.op x x) := by grind
  have eq22788 : y = (k y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8893
       have i₂ := eq2911
       grind)
    | exact superpose eq2911 eq8893
    | exact resolve eq8893 eq2911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2911 eq8893
  have eq22817 : y = (k y x) ∨ y = (M.op x x) := by grind
  clear eq22788
  have eq33484 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq334 x
       have i₂ := eq2764
       grind)
    | exact superpose eq2764 eq334
    | exact resolve eq334 eq2764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq2764
  have eq33566 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq33484
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq33484
    | exact resolve eq33484 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33484
  have eq33567 : x = (k x y) := by grind
  clear eq33566
  have eq42867 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq551 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq42920 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq42867 (σ x)
       have i₂ := eq2766
       grind)
    | exact superpose eq2766 eq42867
    | exact resolve eq42867 eq2766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2766
  have eq43009 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq42920
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq42920
    | exact resolve eq42920 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42920
  have eq43680 : (τ (σ y)) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9 (k y x)
       have i₂ := eq43009
       grind)
    | exact superpose eq43009 eq9
    | exact resolve eq9 eq43009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43009
  have eq43730 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq43680
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq43680
    | exact resolve eq43680 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43680
  have eq45305 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq60 (σ x) (σ x)
       have i₂ := eq2765
       grind)
    | exact superpose eq2765 eq60
    | exact resolve eq60 eq2765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq2765
  have eq45330 : (σ y) = (σ (k y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq45305
       have i₂ := eq13 y y
       grind)
    | exact superpose eq13 eq45305
    | exact resolve eq45305 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45305
  have eq45502 : (k y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq45330
       grind)
    | exact superpose eq45330 eq9
    | exact resolve eq9 eq45330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45330
  have eq45553 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq45502
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq45502
    | exact resolve eq45502 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45502
  have eq45556 : y = (k y y) := by
    first
    | (have j1 := eq91 y y
       grind)
    | (have r₁ := eq45553
       have r₂ := eq91 y y
       grind)
    | exact resolve eq45553 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq45553
  have eq45653 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq290 y
       have i₂ := eq45556
       grind)
    | exact superpose eq45556 eq290
    | (have j0 := eq290 y
       grind)
    | exact resolve eq290 eq45556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq45675 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1169 y y
       have i₂ := eq45556
       grind)
    | exact superpose eq45556 eq1169
    | (have j0 := eq1169 y x
       grind)
    | exact resolve eq1169 eq45556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169 eq45556
  have eq45677 : y = (M.op y y) := by grind
  clear eq45675
  have eq45683 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq45653
  have eq45773 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ y = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq428 y x y
       have i₂ := eq45677
       grind)
    | exact superpose eq45677 eq428
    | exact resolve eq428 eq45677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428 eq45677
  have eq47393 : y = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq22817
       have i₂ := eq45773 x
       grind)
    | exact superpose eq45773 eq22817
    | (have j1 := eq45773 x
       grind)
    | exact resolve eq22817 eq45773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22817
  have eq47398 : y = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq43730
       have i₂ := eq45773 x
       grind)
    | exact superpose eq45773 eq43730
    | (have j1 := eq45773 x
       grind)
    | exact resolve eq43730 eq45773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43730 eq45773
  have eq47466 : y = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq47398
  have eq47469 : y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq47393
  have eq47635 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq51 y x
       have i₂ := eq47466
       grind)
    | exact superpose eq47466 eq51
    | exact resolve eq51 eq47466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq47466
  have eq47670 : y = (M.op x y) := by grind
  clear eq47635
  have eq47790 : y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3057 x
       have i₂ := eq47469
       grind)
    | exact superpose eq47469 eq3057
    | exact resolve eq3057 eq47469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3057 eq47469
  have eq47835 : y = (M.op x x) := by grind
  clear eq47790
  have eq47952 : y = (k y x) := by
    first
    | (have i₁ := eq42867 x
       have i₂ := eq47835
       grind)
    | exact superpose eq47835 eq42867
    | exact resolve eq42867 eq47835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42867 eq47835
  have eq48198 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq5406 X0
       have i₂ := eq33567
       grind)
    | exact superpose eq33567 eq5406
    | (have j0 := eq5406 X0
       grind)
    | exact resolve eq5406 eq33567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5406 eq33567
  have eq48220 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ (M.op (σ x) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq48198 X0
       have i₂ := eq47670
       grind)
    | exact superpose eq47670 eq48198
    | (have j0 := eq48198 X0
       grind)
    | exact resolve eq48198 eq47670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48198
  have eq48739 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq272 y x X0
       have i₂ := eq47952
       grind)
    | exact superpose eq47952 eq272
    | (have j0 := eq272 y x x
       grind)
    | exact resolve eq272 eq47952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272 eq47952
  have eq48789 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op (σ x) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq48739 X0
       have i₂ := eq45683
       grind)
    | exact superpose eq45683 eq48739
    | (have j0 := eq48739 X0
       grind)
    | exact resolve eq48739 eq45683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48739
  have eq48802 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq48789 X0
       have j1 := eq48220 X0
       grind)
    | (have r₁ := eq48789 X0
       have r₂ := eq48220 X0
       grind)
    | exact resolve eq48789 eq48220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48220 eq48789
  have eq48859 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45683
       have i₂ := eq48802 (σ y)
       grind)
    | exact superpose eq48802 eq45683
    | exact resolve eq45683 eq48802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45683 eq48802
  have eq49143 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq48859
       grind)
    | exact superpose eq48859 eq14
    | exact resolve eq14 eq48859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48859
  have eq49253 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq49143
       have i₂ := eq47670
       grind)
    | exact superpose eq47670 eq49143
    | exact resolve eq49143 eq47670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47670 eq49143
  have eq49254 : False := by grind
  exact eq49254

/-- `Equation3583`: `x ◇ y = z ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_y_x_pxy_Equation3583 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3583 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3583.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op (M.op X0 X0) X1) X3
       have i₂ := eq8 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X2 ∨ (M.op (M.op X0 X0) X1) = (k (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (M.op (M.op X0 X0) X1) X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 (M.op (M.op X0 X0) X1) X2
       grind)
    | (have r₁ := eq11 (M.op (M.op X0 X0) X1) (M.op X0 X1)
       have r₂ := eq8 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq18 X0 X1 x X3
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq24 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq20 (M.op X0 X0) X1 x
       grind)
    | exact superpose eq20 eq8
    | exact resolve eq8 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X0)
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq11
    | (have j0 := eq11 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 X1 (M.op X1 X1)
       have r₂ := eq24 X1 X1
       grind)
    | exact resolve eq11 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq53 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq153 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq46
    | exact resolve eq46 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq167 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op (M.op X0 X0) X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq19 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq168 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq167 X0 X1
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq167
    | exact resolve eq167 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq167
  have eq213 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X2 (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 (σ X1) (σ X0) x
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq20
    | (have j1 := eq30 X1 X0
       grind)
    | exact resolve eq20 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq30 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq292 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq37 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq338 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq53 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq292 (σ X0)
       grind)
    | exact superpose eq292 eq53
    | exact resolve eq53 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq292
  have eq341 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq338 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq338
    | exact resolve eq338 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq470 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq215 (M.op X0 X1)
       have i₂ := eq168 X0 X1
       grind)
    | exact superpose eq168 eq215
    | (have j0 := eq215 (M.op X0 X1)
       grind)
    | exact resolve eq215 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq215
  have eq475 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq470 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq489 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq43
    | exact resolve eq43 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq524 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq489 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq489
    | (have j0 := eq489 X0 X1
       grind)
    | exact resolve eq489 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq691 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq213 y x X0
       grind)
    | exact superpose eq213 eq14
    | (have j1 := eq213 y x X0
       grind)
    | exact resolve eq14 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq213 X1 X1 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq758 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 (σ (M.op X0 X1)) (σ (M.op X0 X1)) x
       have i₂ := eq475 X0 X1
       grind)
    | exact superpose eq475 eq20
    | exact resolve eq20 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq4109 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq707 (τ X0) (τ X1)
       have i₂ := eq153 X1 X0
       grind)
    | exact superpose eq153 eq707
    | (have j0 := eq707 (τ X0) (τ X1)
       grind)
    | exact resolve eq707 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq707
  have eq4130 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4109 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq4109
    | (have j0 := eq4109 X0 X1
       grind)
    | exact resolve eq4109 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4109
  have eq4139 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4130 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4130
    | (have j0 := eq4130 X0 X1
       grind)
    | exact resolve eq4130 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4130
  have eq4143 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4139 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4139
    | (have j0 := eq4139 X0 X1
       grind)
    | exact resolve eq4139 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4139
  have eq4144 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4143 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4143
    | (have j0 := eq4143 X0 X1
       grind)
    | exact resolve eq4143 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4143
  have eq4657 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq691 X0
       have i₂ := eq524 x y
       grind)
    | exact superpose eq524 eq691
    | (have j0 := eq691 X0
       have j1 := eq524 x y
       grind)
    | (have r₁ := eq691 X0
       have r₂ := eq524 x y
       grind)
    | exact resolve eq691 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524 eq691
  have eq4658 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq4657 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4657
  have eq5061 : y = (k y (τ (σ y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq341 y
       have i₂ := eq4658 (σ y)
       grind)
    | exact superpose eq4658 eq341
    | exact resolve eq341 eq4658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341 eq4658
  have eq5067 : y = (k y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq5061
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq5061
    | exact resolve eq5061 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5061
  have eq5162 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq4144 y y
       have i₂ := eq5067
       grind)
    | exact superpose eq5067 eq4144
    | (have j0 := eq4144 y y
       grind)
    | (have r₁ := eq4144 y y
       have r₂ := eq5067
       grind)
    | exact resolve eq4144 eq5067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4144 eq5067
  have eq5163 : y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq5162
  have eq5327 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq20 y y x
       have i₂ := eq5163
       grind)
    | exact superpose eq5163 eq20
    | exact resolve eq20 eq5163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5163
  have eq5476 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq20 y x x
       have i₂ := eq5327 X0
       grind)
    | exact superpose eq5327 eq20
    | (have j1 := eq5327 X0
       grind)
    | exact resolve eq20 eq5327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5327
  have eq5819 : ∀ X0 : G, y ≠ y ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq5476 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5476
  have eq5820 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq5819 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5819
  have eq5853 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) := by
    intro X1
    first
    | (have i₁ := eq758 x y x
       have i₂ := eq5820 x
       grind)
    | exact superpose eq5820 eq758
    | exact resolve eq758 eq5820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq6150 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq5853 (σ x)
       grind)
    | exact superpose eq5853 eq14
    | exact resolve eq14 eq5853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5853
  have eq6155 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq6150
       have i₂ := eq5820 x
       grind)
    | exact superpose eq5820 eq6150
    | exact resolve eq6150 eq5820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5820 eq6150
  have eq6156 : False := by grind
  exact eq6156

/-- `Equation3587`: `x ◇ y = z ◇ ((x ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_y_x_pxy_Equation3587 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3587 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3587.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op (M.op X0 X1) X1) X3
       have i₂ := eq8 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq18 X0 X1 x X3
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq25 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq20 (M.op X0 X1) X1 x
       grind)
    | exact superpose eq20 eq8
    | exact resolve eq8 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X1)
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq11
    | (have j0 := eq11 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq11 X1 (M.op X0 X1)
       have r₂ := eq25 X0 X1
       grind)
    | exact resolve eq11 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq44 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq46 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq44 x (M.op X0 X1)
       have i₂ := eq20 X0 X1 x
       grind)
    | exact superpose eq20 eq44
    | exact resolve eq44 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq85 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq49
    | exact resolve eq49 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq121 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X2 (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 (σ X1) (σ X0) x
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq20
    | (have j1 := eq32 X1 X0
       grind)
    | exact resolve eq20 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq32 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq141 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 (M.op X1 (σ X0))
       have i₂ := eq44 X1 (σ X0)
       grind)
    | exact superpose eq44 eq64
    | exact resolve eq64 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq64
  have eq153 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq141 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq141
    | exact resolve eq141 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq395 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq124 (M.op X0 X1)
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq124
    | (have j0 := eq124 (M.op X0 X1)
       grind)
    | exact resolve eq124 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq124
  have eq400 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq395 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq414 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq46 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq46
    | exact resolve eq46 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq450 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq414 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq414
    | (have j0 := eq414 X0 X1
       grind)
    | exact resolve eq414 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq613 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq121 y x X0
       grind)
    | exact superpose eq121 eq14
    | (have j1 := eq121 y x X0
       grind)
    | exact resolve eq14 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq626 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq121 X1 X1 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq1431 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 (σ (M.op X0 X1)) (σ (M.op X0 X1)) x
       have i₂ := eq400 X0 X1
       grind)
    | exact superpose eq400 eq20
    | exact resolve eq20 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq3346 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq626 (τ X0) (τ X1)
       have i₂ := eq85 X1 X0
       grind)
    | exact superpose eq85 eq626
    | (have j0 := eq626 (τ X0) (τ X1)
       grind)
    | exact resolve eq626 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq626
  have eq3365 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3346 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq3346
    | (have j0 := eq3346 X0 X1
       grind)
    | exact resolve eq3346 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3346
  have eq3372 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3365 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3365
    | (have j0 := eq3365 X0 X1
       grind)
    | exact resolve eq3365 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3365
  have eq3376 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3372 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3372
    | (have j0 := eq3372 X0 X1
       grind)
    | exact resolve eq3372 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3372
  have eq3377 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3376 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3376
    | (have j0 := eq3376 X0 X1
       grind)
    | exact resolve eq3376 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3376
  have eq3871 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq613 X0
       have i₂ := eq450 x y
       grind)
    | exact superpose eq450 eq613
    | (have j0 := eq613 X0
       have j1 := eq450 x y
       grind)
    | (have r₁ := eq613 X0
       have r₂ := eq450 x y
       grind)
    | exact resolve eq613 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450 eq613
  have eq3872 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq3871 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3871
  have eq4360 : y = (k y (τ (σ y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq153 y x
       have i₂ := eq3872 x
       grind)
    | exact superpose eq3872 eq153
    | exact resolve eq153 eq3872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq3872
  have eq4391 : y = (k y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq4360
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq4360
    | exact resolve eq4360 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4360
  have eq4552 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq3377 y y
       have i₂ := eq4391
       grind)
    | exact superpose eq4391 eq3377
    | (have j0 := eq3377 y y
       grind)
    | (have r₁ := eq3377 y y
       have r₂ := eq4391
       grind)
    | exact resolve eq3377 eq4391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3377 eq4391
  have eq4553 : y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq4552
  have eq4651 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq20 y y x
       have i₂ := eq4553
       grind)
    | exact superpose eq4553 eq20
    | exact resolve eq20 eq4553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4553
  have eq4695 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq20 y x x
       have i₂ := eq4651 X0
       grind)
    | exact superpose eq4651 eq20
    | (have j1 := eq4651 X0
       grind)
    | exact resolve eq20 eq4651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4651
  have eq4859 : ∀ X0 : G, y ≠ y ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq4695 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4695
  have eq4860 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq4859 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4859
  have eq4945 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) := by
    intro X1
    first
    | (have i₁ := eq1431 x y x
       have i₂ := eq4860 x
       grind)
    | exact superpose eq4860 eq1431
    | exact resolve eq1431 eq4860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1431
  have eq5245 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq4945 (σ x)
       grind)
    | exact superpose eq4945 eq14
    | exact resolve eq14 eq4945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4945
  have eq5255 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq5245
       have i₂ := eq4860 x
       grind)
    | exact superpose eq4860 eq5245
    | exact resolve eq5245 eq4860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4860 eq5245
  have eq5256 : False := by grind
  exact eq5256

/-- `Equation3591`: `x ◇ y = z ◇ ((x ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_pxx_pxy_Equation3591 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3591 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3591.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X2) X1)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X0 X2) X1) (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op (M.op X0 X2) X1)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 (M.op X2 X3)) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op (M.op X0 (M.op X2 X3)) X1) X3
       have i₂ := eq8 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) X1
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq41 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq69 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X0) X1) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq47 X0 (τ X1) X2
       grind)
    | exact superpose eq47 eq16
    | (have j1 := eq47 (σ X0) X1 X2
       grind)
    | exact resolve eq16 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (τ X0) = (k (τ X0) X1) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq47 X0 (σ X1) X2
       grind)
    | exact superpose eq47 eq20
    | (have j1 := eq47 (τ X0) X1 X2
       grind)
    | exact resolve eq20 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq47 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq47 eq13
    | (have j1 := eq47 (σ X0) X2 X2
       grind)
    | exact resolve eq13 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq47 X0 X2 (τ X1)
       grind)
    | exact superpose eq47 eq16
    | (have j1 := eq47 X0 X2 X2
       grind)
    | exact resolve eq16 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq84 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op (M.op X0 X2) X1)) ∨ (k X0 X3) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X0 X2 X0 X1
       have i₂ := eq12 X0 X3
       grind)
    | exact superpose eq12 eq21
    | (have j1 := eq12 X0 X3
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op (M.op (M.op (M.op (M.op X4 X0) X5) X2) (M.op (M.op X4 X5) X1)) (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq21 (M.op (M.op X4 X0) X5) (M.op (M.op X4 X5) X1) X2 X3
       have i₂ := eq21 X4 X5 X0 X1
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 (M.op X3 X4)) X1)) = (M.op (M.op (M.op X3 X2) X4) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq21 X3 X4 X2 (M.op (M.op X0 (M.op X3 X4)) X1)
       have i₂ := eq8 X0 X1 (M.op X3 X4)
       grind)
    | exact superpose eq8 eq21
    | exact resolve eq21 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op (M.op X2 X3) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X2 X0) (M.op (M.op X2 X3) X1) X3
       have i₂ := eq21 X2 X3 X0 X1
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X0) X3) X4) = (M.op (M.op (M.op X2 X3) X1) (M.op (M.op X0 X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op (M.op X2 X0) X3) X4 (M.op (M.op X2 X3) X1)
       have i₂ := eq21 X2 X3 X0 X1
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op (M.op X0 X1) (M.op (M.op (M.op X4 X0) X5) (M.op (M.op X4 X5) X1))) X3)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq91 X0 X1 X2 X3 X4 X5
       have i₂ := eq93 (M.op X0 X1) X3 X2 (M.op (M.op X4 X0) X5) (M.op (M.op X4 X5) X1)
       grind)
    | exact superpose eq93 eq91
    | exact resolve eq91 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq109 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op X2 X1)) ∨ (k X0 X3) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq84 X0 X1 X2 X3
       have i₂ := eq96 X2 X1 X0 X2
       grind)
    | exact superpose eq96 eq84
    | (have j0 := eq84 X0 X1 X2 X3
       grind)
    | exact resolve eq84 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq110 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq102 X0 X1 X2 X3 x x
       have i₂ := eq21 x x X0 X1
       grind)
    | exact superpose eq21 eq102
    | exact resolve eq102 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq129 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 (M.op X3 X0)) X2) (M.op X4 X5)) = (M.op X3 (M.op (M.op X4 (M.op X0 (M.op X1 X2))) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq22 X4 X5 X3 (M.op (M.op X1 (M.op X3 X0)) X2)
       have i₂ := eq22 X1 X2 X3 X0
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op (M.op X2 X0) X3) X4)) = (M.op (M.op X2 X3) (M.op (M.op X0 X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq22 (M.op (M.op X2 X0) X3) X4 (M.op X2 X3) X1
       have i₂ := eq21 X2 X3 X0 X1
       grind)
    | exact superpose eq21 eq22
    | exact resolve eq22 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 (M.op X3 X0)) X2) X4) = (M.op (M.op (M.op X0 (M.op X1 X2)) X5) (M.op (M.op X3 X5) X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq21 X3 X5 (M.op (M.op X1 (M.op X3 X0)) X2) X4
       have i₂ := eq22 X1 X2 X3 X0
       grind)
    | exact superpose eq22 eq21
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X1 (M.op (M.op X4 X5) X0)) X2)) = (M.op (M.op (M.op X4 X3) X5) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq21 X4 X5 X3 (M.op (M.op X1 (M.op (M.op X4 X5) X0)) X2)
       have i₂ := eq22 X1 X2 (M.op X4 X5) X0
       grind)
    | exact superpose eq22 eq21
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X1 (M.op (M.op X4 X5) X0)) X2)) = (M.op X3 (M.op (M.op X0 (M.op X4 X5)) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq144 X0 X1 X2 X3 X4 X5
       have i₂ := eq93 X0 (M.op X1 X2) X3 X4 X5
       grind)
    | exact superpose eq93 eq144
    | exact resolve eq144 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq150 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 (M.op X3 X0)) X2) X4) = (M.op (M.op (M.op X0 X3) (M.op X1 X2)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq141 X0 X1 X2 X3 X4 x
       have i₂ := eq98 X3 x X0 (M.op X1 X2) X4
       grind)
    | exact superpose eq98 eq141
    | exact resolve eq141 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq141
  have eq157 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X4 (M.op X0 (M.op X1 X2))) X5)) = (M.op (M.op X3 X0) (M.op (M.op X4 (M.op X1 X2)) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq129 X0 X1 X2 X3 X4 X5
       have i₂ := eq93 X4 X5 (M.op X3 X0) X1 X2
       grind)
    | exact superpose eq93 eq129
    | exact resolve eq129 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq173 : ∀ X0 X1 X2 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq69 X0 (σ X1) X2
       grind)
    | exact superpose eq69 eq13
    | (have j1 := eq69 X0 X1 X2
       grind)
    | exact resolve eq13 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq224 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) X2) = (k (σ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 (σ X0) X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq70
    | (have j0 := eq70 (σ X0) X1 X2
       grind)
    | exact resolve eq70 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq289 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq43 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq957 : ∀ X0 X1 X2 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq75 X1 (σ X0) X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq75
    | (have j0 := eq75 X1 X1 X2
       grind)
    | exact resolve eq75 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq1036 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq957 X0 X1 X2
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq957
    | (have j0 := eq957 X0 X1 X2
       grind)
    | exact resolve eq957 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq1260 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X0) X1) ∨ (σ (k X0 X2)) = (σ (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq1036 X2 X0 (τ X1)
       grind)
    | exact superpose eq1036 eq16
    | (have j1 := eq1036 X2 X0 X2
       grind)
    | exact resolve eq16 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq1323 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X2) X1) (M.op X3 X4)) = (M.op (M.op X2 X3) (M.op (M.op X0 X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq96 X3 X4 X2 (M.op (M.op X0 X2) X1)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq96
    | exact resolve eq96 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1357 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X2 (M.op X0 X1)
       have i₂ := eq96 X1 X2 X0 (M.op X0 X1)
       grind)
    | exact superpose eq96 eq8
    | exact resolve eq8 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1358 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X1) X4)) = (M.op (M.op X3 X0) (M.op (M.op X0 (M.op X1 X2)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq22 (M.op X3 X1) X4 (M.op X3 X0) X2
       have i₂ := eq96 X1 X2 X3 X0
       grind)
    | exact superpose eq96 eq22
    | exact resolve eq22 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1360 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op (M.op (M.op X3 X0) X2) (M.op (M.op X0 (M.op X1 X2)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op X3 X1) X4 (M.op (M.op X3 X0) X2)
       have i₂ := eq96 X1 X2 X3 X0
       grind)
    | exact superpose eq96 eq8
    | exact resolve eq8 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1363 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 X0) X2) (M.op X4 X5)) = (M.op (M.op X3 X1) (M.op (M.op X4 (M.op X0 (M.op X1 X2))) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq22 X4 X5 (M.op X3 X1) (M.op (M.op X3 X0) X2)
       have i₂ := eq96 X1 X2 X3 X0
       grind)
    | exact superpose eq96 eq22
    | exact resolve eq22 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq1372 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 X0) X2) (M.op X4 X5)) = (M.op X3 (M.op (M.op X4 (M.op X1 (M.op X0 (M.op X1 X2)))) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1363 X0 X1 X2 X3 X4 X5
       have i₂ := eq157 X1 X0 (M.op X1 X2) X3 X4 X5
       grind)
    | exact superpose eq157 eq1363
    | exact resolve eq1363 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1363
  have eq1375 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op X0 (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X2)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1360 X0 X1 X2 X3 X4
       have i₂ := eq93 (M.op X0 (M.op X1 X2)) X4 X0 X3 X2
       grind)
    | exact superpose eq93 eq1360
    | exact resolve eq1360 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1360
  have eq1377 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X1) X4)) = (M.op X3 (M.op (M.op X0 (M.op X0 (M.op X1 X2))) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1358 X0 X1 X2 X3 X4
       have i₂ := eq157 X0 X1 X2 X3 X0 X4
       grind)
    | exact superpose eq157 eq1358
    | exact resolve eq1358 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq1358
  have eq1392 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 (M.op X0 X1)) X4)) = (M.op (M.op X2 X3) (M.op (M.op X0 X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1323 X0 X1 X2 X3 X4
       have i₂ := eq93 X3 X4 X2 X0 X1
       grind)
    | exact superpose eq93 eq1323
    | exact resolve eq1323 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323
  have eq1397 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X4 (M.op X1 (M.op X0 (M.op X1 X2)))) X5)) = (M.op X0 (M.op (M.op X4 (M.op X3 X2)) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1372 X0 X1 X2 X3 X4 X5
       have i₂ := eq93 X4 X5 X0 X3 X2
       grind)
    | exact superpose eq93 eq1372
    | exact resolve eq1372 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq1372
  have eq1400 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op X0 (M.op (M.op (M.op X2 X1) (M.op X0 (M.op X3 X2))) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1375 X0 X1 X2 X3 X4
       have i₂ := eq150 X2 X0 (M.op X3 X2) X1 X4
       grind)
    | (have i₁ := eq1375 X0 X1 X2 X1 X4
       have i₂ := eq150 X0 X1 X2 (M.op X1 X2) X4
       grind)
    | exact superpose eq150 eq1375
    | exact resolve eq1375 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375
  have eq1410 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op (M.op X3 X2) (M.op (M.op X2 X1) X4)) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq1400 x X1 X2 X3 X4
       have i₂ := eq22 (M.op X2 X1) X4 x (M.op X3 X2)
       grind)
    | exact superpose eq22 eq1400
    | exact resolve eq1400 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400
  have eq1415 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op X3 (M.op (M.op X2 (M.op X2 X1)) X4)) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq1410 X1 X2 X3 X4
       have i₂ := eq1392 X2 X1 X3 X2 X4
       grind)
    | (have i₁ := eq1410 (M.op x X1) X3 X3 X4
       have i₂ := eq1392 x X1 (M.op X3 X3) X3 X4
       grind)
    | exact superpose eq1392 eq1410
    | exact resolve eq1410 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410
  have eq1423 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op (M.op X1 (M.op X3 X0)) X2) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1357 X3 (M.op (M.op X1 (M.op X3 X0)) X2) X4
       have i₂ := eq22 X1 X2 X3 X0
       grind)
    | exact superpose eq22 eq1357
    | exact resolve eq1357 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1435 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X3) X1)) = (M.op (M.op X2 X3) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1357 X2 X3 (M.op (M.op X0 X3) X1)
       have i₂ := eq8 X0 X1 X3
       grind)
    | exact superpose eq8 eq1357
    | exact resolve eq1357 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1452 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op (M.op X0 X2) X3) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X0 X3 X2 (M.op X3 X1)
       have i₂ := eq1357 X0 X3 X1
       grind)
    | exact superpose eq1357 eq21
    | exact resolve eq21 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1454 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X0 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X0 X1) X0
       have i₂ := eq1357 X2 X0 X1
       grind)
    | exact superpose eq1357 eq8
    | exact resolve eq8 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1457 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) X3)) = (M.op X2 (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 (M.op X0 X1) X3 X1 X2
       have i₂ := eq1357 X0 X1 X2
       grind)
    | exact superpose eq1357 eq22
    | exact resolve eq22 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1458 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op x x) X1
       have i₂ := eq1357 x x x
       grind)
    | exact superpose eq1357 eq11
    | (have r₁ := eq11 (M.op x x) X1
       have r₂ := eq1357 x x x
       grind)
    | exact resolve eq11 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1461 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X1) X3) = (M.op (M.op (M.op X0 X1) X4) (M.op (M.op (M.op X0 X2) X4) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq21 (M.op X0 X2) X4 (M.op X2 X1) X3
       have i₂ := eq1357 X0 X2 X1
       grind)
    | exact superpose eq1357 eq21
    | exact resolve eq21 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1470 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1458 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1458
  have eq1475 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X1) X3) = (M.op (M.op X0 X4) (M.op (M.op X2 (M.op (M.op X0 X1) X4)) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1461 X0 X1 X2 X3 X4
       have i₂ := eq135 X2 (M.op (M.op X0 X1) X4) X0 X4 X3
       grind)
    | (have i₁ := eq1461 X0 X1 X2 X4 X1
       have i₂ := eq135 (M.op X0 X2) X1 (M.op X0 X1) X1 X4
       grind)
    | exact superpose eq135 eq1461
    | exact resolve eq1461 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq1461
  have eq1479 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X0 (M.op (M.op (M.op X0 X2) X3) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1452 X0 X1 X2 X3
       have i₂ := eq1454 X0 X1 (M.op (M.op X0 X2) X3)
       grind)
    | (have i₁ := eq1452 X0 X1 X2 X3
       have i₂ := eq1454 (M.op (M.op X0 X2) X3) X1 X0
       grind)
    | exact superpose eq1454 eq1452
    | exact resolve eq1452 eq1454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452 eq1454
  have eq1492 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op X2 (M.op (M.op (M.op X1 (M.op X3 X0)) (M.op X0 (M.op X1 X2))) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1423 X0 X1 X2 X3 X4
       have i₂ := eq1457 (M.op X1 (M.op X3 X0)) (M.op X0 (M.op X1 X2)) X2 X4
       grind)
    | (have i₁ := eq1423 X0 X1 X2 X3 X4
       have i₂ := eq1457 (M.op X1 (M.op X3 X0)) X2 (M.op X0 (M.op X1 X2)) X4
       grind)
    | exact superpose eq1457 eq1423
    | exact resolve eq1423 eq1457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1423
  have eq1498 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X1) X3) = (M.op (M.op X0 X4) (M.op (M.op X4 (M.op X0 X1)) (M.op X2 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1475 X0 X1 X2 X3 X4
       have i₂ := eq148 X4 X2 X3 (M.op X0 X4) X0 X1
       grind)
    | (have i₁ := eq1475 X0 X1 X0 (M.op X1 X2) x
       have i₂ := eq148 X0 X1 X2 (M.op X0 x) (M.op X0 X1) x
       grind)
    | exact superpose eq148 eq1475
    | exact resolve eq1475 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475
  have eq1508 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op X2 (M.op (M.op (M.op X0 X3) (M.op X1 (M.op X0 (M.op X1 X2)))) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1492 X0 X1 X2 X3 X4
       have i₂ := eq150 X0 X1 (M.op X0 (M.op X1 X2)) X3 X4
       grind)
    | (have i₁ := eq1492 X1 X0 X2 X3 X4
       have i₂ := eq150 X0 X1 (M.op X0 X2) (M.op X3 X1) X4
       grind)
    | exact superpose eq150 eq1492
    | exact resolve eq1492 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq1492
  have eq1512 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X1) X3) = (M.op X0 (M.op (M.op X4 (M.op X4 (M.op X0 X1))) (M.op X2 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1498 X0 X1 X2 X3 X4
       have i₂ := eq1392 X4 (M.op X0 X1) X0 X4 (M.op X2 X3)
       grind)
    | (have i₁ := eq1498 X0 X1 X2 X3 X3
       have i₂ := eq1392 X0 X1 (M.op X0 X3) X3 (M.op X2 X3)
       grind)
    | exact superpose eq1392 eq1498
    | exact resolve eq1498 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392 eq1498
  have eq1516 : ∀ X0 X2 X3 X4 : G, (M.op X3 X4) = (M.op X0 (M.op (M.op (M.op X0 X3) (M.op X2 X2)) X4)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq1508 X0 x X2 X3 X4
       have i₂ := eq1397 X0 x X2 X2 (M.op X0 X3) X4
       grind)
    | exact superpose eq1397 eq1508
    | exact resolve eq1508 eq1397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397 eq1508
  have eq1518 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X3) = (M.op X1 (M.op (M.op X0 X0) (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1512 X0 X1 X2 X3 x
       have i₂ := eq1377 x X0 X1 X0 (M.op X2 X3)
       grind)
    | exact superpose eq1377 eq1512
    | exact resolve eq1512 eq1377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377 eq1512
  have eq1521 : ∀ X2 X3 X4 : G, (M.op X3 X4) = (M.op X3 (M.op (M.op X2 X2) X4)) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq1516 x X2 X3 X4
       have i₂ := eq1479 x X4 X3 (M.op X2 X2)
       grind)
    | exact superpose eq1479 eq1516
    | exact resolve eq1516 eq1479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479 eq1516
  have eq1523 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X3) = (M.op X1 (M.op X0 (M.op (M.op X2 X0) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1518 X0 X1 X2 X3
       have i₂ := eq1435 X2 X3 X0 X0
       grind)
    | (have i₁ := eq1518 X0 X1 (M.op X0 X3) X1
       have i₂ := eq1435 X0 X1 (M.op X0 X0) X3
       grind)
    | exact superpose eq1435 eq1518
    | exact resolve eq1518 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435 eq1518
  have eq1525 : ∀ X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op (M.op X2 X1) X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq1523 x X1 X2 X3
       have i₂ := eq8 X2 X3 x
       grind)
    | exact superpose eq8 eq1523
    | exact resolve eq1523 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1523
  have eq1572 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X3 X4) (M.op X3 X4)) X1) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X0 X2 (M.op (M.op (M.op X3 X4) (M.op X3 X4)) X1)
       have i₂ := eq110 X3 X4 X0 X1
       grind)
    | exact superpose eq110 eq8
    | exact resolve eq8 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq1612 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X2) = (M.op X1 (M.op (M.op X0 (M.op (M.op (M.op X3 X4) (M.op X3 X4)) X1)) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1572 X0 X1 X2 X3 X4
       have i₂ := eq1457 X0 (M.op (M.op (M.op X3 X4) (M.op X3 X4)) X1) X1 X2
       grind)
    | (have i₁ := eq1572 X0 X1 X2 X3 X4
       have i₂ := eq1457 X0 X1 (M.op (M.op (M.op X3 X4) (M.op X3 X4)) X1) X2
       grind)
    | exact superpose eq1457 eq1572
    | exact resolve eq1572 eq1457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1572
  have eq1650 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X2) = (M.op X1 (M.op (M.op X1 (M.op (M.op X3 X4) (M.op X3 X4))) (M.op X0 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1612 X0 X1 X2 X3 X4
       have i₂ := eq148 X1 X0 X2 X1 (M.op X3 X4) (M.op X3 X4)
       grind)
    | (have i₁ := eq1612 X0 x (M.op X1 X2) X3 X4
       have i₂ := eq148 X0 X1 X2 x (M.op (M.op X3 X4) (M.op X3 X4)) x
       grind)
    | exact superpose eq148 eq1612
    | exact resolve eq1612 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1612
  have eq1681 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X2) = (M.op X1 (M.op (M.op (M.op X3 X4) (M.op X3 X4)) (M.op X1 (M.op X0 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1650 X0 X1 X2 X3 X4
       have i₂ := eq148 (M.op X3 X4) X1 (M.op X0 X2) X1 X3 X4
       grind)
    | (have i₁ := eq1650 X1 X0 X2 X3 X4
       have i₂ := eq148 X0 X1 X2 X0 (M.op X3 X4) (M.op X3 X4)
       grind)
    | exact superpose eq148 eq1650
    | exact resolve eq1650 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq1650
  have eq1707 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1681 X0 X1 X2 x x
       have i₂ := eq1521 (M.op x x) X1 (M.op X1 (M.op X0 X2))
       grind)
    | (have i₁ := eq1681 X0 x X2 x x
       have i₂ := eq1521 X2 x (M.op (M.op (M.op x x) (M.op x x)) (M.op x (M.op X0 X2)))
       grind)
    | exact superpose eq1521 eq1681
    | exact resolve eq1681 eq1521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1521 eq1681
  have eq1874 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq289 (M.op X0 X0)
       have i₂ := eq1470 X0 (M.op X0 X0)
       grind)
    | exact superpose eq1470 eq289
    | (have j0 := eq289 (M.op X0 X0)
       grind)
    | exact resolve eq289 eq1470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470
  have eq1883 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq289 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq289
    | (have j0 := eq289 (τ X0)
       grind)
    | exact resolve eq289 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq289
  have eq1890 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1874 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1874
  have eq1897 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1883 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1883
    | (have j0 := eq1883 X0
       grind)
    | exact resolve eq1883 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1883
  have eq1905 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1897 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1897
    | (have j0 := eq1897 X0
       grind)
    | exact resolve eq1897 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1897
  have eq2074 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = X0 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1707 X0 X1 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq1707
    | (have j1 := eq12 X0 X2
       grind)
    | exact resolve eq1707 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2249 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ X1 ∨ (M.op X0 (M.op X0 X1)) = (k X1 X2) ∨ (M.op X1 X3) = (k X1 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 X1 X1
       have i₂ := eq109 X1 X1 X2 X3
       grind)
    | exact superpose eq109 eq11
    | (have j1 := eq109 X1 X1 X2 X3
       grind)
    | exact resolve eq11 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq2391 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (k X1 X2) ∨ (M.op X1 X3) = (k X1 X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq2249 X0 X1 X2 X3
       have j1 := eq2074 X1 X1 X3
       grind)
    | (have r₁ := eq2249 X1 X0 X2 X3
       have r₂ := eq2074 X0 X1 X2
       grind)
    | exact resolve eq2249 eq2074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2074 eq2249
  have eq4512 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq72 x y X0
       grind)
    | exact superpose eq72 eq14
    | (have j1 := eq72 x x X0
       grind)
    | exact resolve eq14 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq4592 : ∀ X0 : G, (σ x) = (k (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq4512 X0
       have j1 := eq1260 x X0 x
       grind)
    | (have r₁ := eq4512 X0
       have r₂ := eq1260 x x y
       grind)
    | exact resolve eq4512 eq1260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260 eq4512
  have eq4638 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1905 (σ x)
       have i₂ := eq4592 (σ x)
       grind)
    | exact superpose eq4592 eq1905
    | (have j0 := eq1905 (σ x)
       grind)
    | (have r₁ := eq1905 (σ x)
       have r₂ := eq4592 (σ x)
       grind)
    | exact resolve eq1905 eq4592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4654 : ∀ X0 : G, (τ (σ x)) = (k (τ (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq20 (σ x) X0
       have i₂ := eq4592 (σ X0)
       grind)
    | exact superpose eq4592 eq20
    | exact resolve eq20 eq4592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4592
  have eq4657 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4638
  have eq4658 : ∀ X0 : G, x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq4654 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq4654
    | exact resolve eq4654 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4654
  have eq4809 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1905 x
       have i₂ := eq4658 x
       grind)
    | exact superpose eq4658 eq1905
    | (have j0 := eq1905 x
       grind)
    | (have r₁ := eq1905 x
       have r₂ := eq4658 x
       grind)
    | exact resolve eq1905 eq4658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1905 eq4658
  have eq4828 : x = (M.op x x) := by grind
  clear eq4809
  have eq4850 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op x X1) (M.op (M.op x X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 x X1 x X0
       have i₂ := eq4828
       grind)
    | exact superpose eq4828 eq21
    | exact resolve eq21 eq4828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq4865 : ∀ X0 : G, x = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq1707 x x x
       have i₂ := eq4828
       grind)
    | exact superpose eq4828 eq1707
    | exact resolve eq1707 eq4828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4875 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op (M.op x (M.op x X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4850 X0 X1
       have i₂ := eq1457 x (M.op x X1) X1 X0
       grind)
    | (have i₁ := eq4850 X0 X1
       have i₂ := eq1457 x X1 (M.op x X1) X0
       grind)
    | exact superpose eq1457 eq4850
    | exact resolve eq4850 eq1457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1457 eq4850
  have eq4880 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4875 X0 X1
       have i₂ := eq1415 X1 x X1 X0
       grind)
    | (have i₁ := eq4875 X0 (M.op x X1)
       have i₂ := eq1415 X1 x x (M.op (M.op x (M.op x (M.op x X1))) X0)
       grind)
    | exact superpose eq1415 eq4875
    | exact resolve eq4875 eq1415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1415 eq4875
  have eq4882 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4880 X0 X1
       have i₂ := eq1525 X1 X1 X0
       grind)
    | exact superpose eq1525 eq4880
    | exact resolve eq4880 eq1525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1525 eq4880
  have eq9533 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq1357 (σ x) (σ x) X0
       have i₂ := eq4657
       grind)
    | exact superpose eq4657 eq1357
    | exact resolve eq1357 eq4657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357
  have eq9538 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq1707 (σ x) x (σ x)
       have i₂ := eq4657
       grind)
    | exact superpose eq4657 eq1707
    | exact resolve eq1707 eq4657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1707 eq4657
  have eq9541 : (σ x) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq9538 x
       have i₂ := eq4882 (σ x) x
       grind)
    | exact superpose eq4882 eq9538
    | exact resolve eq9538 eq4882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9538
  have eq9544 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq9533 X0
       have i₂ := eq4882 X0 (σ x)
       grind)
    | exact superpose eq4882 eq9533
    | exact resolve eq9533 eq4882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9533
  have eq15965 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq9544 (σ y)
       grind)
    | exact superpose eq9544 eq14
    | exact resolve eq14 eq9544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9544
  have eq287924 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op x (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4882 (σ (M.op X0 X0)) (σ (M.op X0 X0))
       have i₂ := eq1890 X0
       grind)
    | exact superpose eq1890 eq4882
    | exact resolve eq4882 eq1890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287931 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op x (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq287924 X0
       have i₂ := eq1890 X0
       grind)
    | exact superpose eq1890 eq287924
    | exact resolve eq287924 eq1890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1890 eq287924
  have eq295040 : ∀ X0 X1 : G, (σ X0) = (M.op x (σ X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq287931 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq287931
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq287931 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287931
  have eq297236 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 (M.op X2 X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2391 X0 X0 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2391
  have eq297239 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op x X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq297236 X0 X1 x
       have i₂ := eq4882 X0 x
       grind)
    | exact superpose eq4882 eq297236
    | (have j0 := eq297236 X0 X1 x
       grind)
    | (have r₁ := eq297236 X1 (M.op X1 (M.op x X1)) x
       have r₂ := eq4882 (M.op x X1) X1
       grind)
    | (have r₁ := eq297236 x x X1
       have r₂ := eq4882 x X1
       grind)
    | exact resolve eq297236 eq4882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297236
  have eq307777 : ∀ X0 X1 : G, (M.op x X0) ≠ (M.op x X1) ∨ (k X1 (M.op X1 X0)) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq297239 X1 (M.op X1 X0)
       have i₂ := eq4882 X0 X1
       grind)
    | exact superpose eq4882 eq297239
    | (have r₁ := eq297239 X0 (M.op X0 X0)
       have r₂ := eq4882 X0 X0
       grind)
    | exact resolve eq297239 eq4882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4882 eq297239
  have eq499887 : ∀ X0 : G, (M.op x X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq307777 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307777
  have eq500314 : ∀ X0 X1 : G, (σ X0) = (σ (M.op x X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq173 X0 (M.op X0 X0) X1
       have i₂ := eq499887 X0
       grind)
    | exact superpose eq499887 eq173
    | (have j0 := eq173 X0 X1 X1
       grind)
    | exact resolve eq173 eq499887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq501046 : ∀ X0 : G, (σ y) ≠ (M.op x (σ y)) ∨ (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq15965
       have i₂ := eq500314 y X0
       grind)
    | exact superpose eq500314 eq15965
    | (have j1 := eq500314 y X0
       grind)
    | exact resolve eq15965 eq500314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500314
  have eq501148 : ∀ X0 : G, (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq501046 X0
       have j1 := eq295040 y X0
       grind)
    | (have r₁ := eq501046 X0
       have r₂ := eq295040 y x
       grind)
    | exact resolve eq501046 eq295040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295040 eq501046
  have eq501403 : ∀ X0 X1 : G, y = (M.op y X0) ∨ (k (σ y) X1) = (M.op (σ y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq224 y X0 X1
       have i₂ := eq501148 X0
       grind)
    | exact superpose eq501148 eq224
    | (have j0 := eq224 y X1 X1
       grind)
    | exact resolve eq224 eq501148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq507281 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq4865 y
       have i₂ := eq501403 (M.op y x) X0
       grind)
    | exact superpose eq501403 eq4865
    | (have j1 := eq501403 X0 X0
       grind)
    | exact resolve eq4865 eq501403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4865 eq501403
  have eq507498 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq507281 (σ X0)
       grind)
    | exact superpose eq507281 eq13
    | exact resolve eq13 eq507281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507281
  have eq507627 : ∀ X0 : G, (σ (M.op y X0)) = (M.op (σ y) (σ X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq507498 X0
       have i₂ := eq501148 X0
       grind)
    | exact superpose eq501148 eq507498
    | exact resolve eq507498 eq501148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501148 eq507498
  have eq507791 : (M.op x (σ y)) = (k (σ y) (σ (M.op y y))) ∨ x = y := by
    first
    | (have i₁ := eq499887 (σ y)
       have i₂ := eq507627 y
       grind)
    | exact superpose eq507627 eq499887
    | exact resolve eq499887 eq507627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507627
  have eq507830 : (M.op x (σ y)) = (σ (k y (M.op y y))) ∨ x = y := by
    first
    | (have i₁ := eq507791
       have i₂ := eq13 y (M.op y y)
       grind)
    | exact superpose eq13 eq507791
    | exact resolve eq507791 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507791
  have eq507880 : (σ (M.op x y)) = (M.op x (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq507830
       have i₂ := eq499887 y
       grind)
    | exact superpose eq499887 eq507830
    | exact resolve eq507830 eq499887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499887 eq507830
  have eq507890 : x = y := by
    first
    | (have r₁ := eq507880
       have r₂ := eq15965
       grind)
    | exact resolve eq507880 eq15965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507880
  have eq507899 : (M.op x (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq15965
       have i₂ := eq507890
       grind)
    | exact superpose eq507890 eq15965
    | exact resolve eq15965 eq507890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15965 eq507890
  have eq507918 : (σ x) ≠ (M.op x (σ x)) := by
    first
    | (have i₁ := eq507899
       have i₂ := eq4828
       grind)
    | exact superpose eq4828 eq507899
    | exact resolve eq507899 eq4828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4828 eq507899
  have eq507924 : False := by grind
  exact eq507924

/-- `Equation3591`: `x ◇ y = z ◇ ((x ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_y_pxy_Equation3591 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3591 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3591.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X2) X1)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq17 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X0 X2) X1) (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op (M.op X0 X2) X1)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 (M.op X2 X3)) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op (M.op X0 (M.op X2 X3)) X1) X3
       have i₂ := eq8 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq24 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X2
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X1
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) X1
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 X2 : G, (k X0 X1) = X1 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq24 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq31 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq29 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq29 eq13
    | (have j1 := eq29 (σ X0) X2 X2
       grind)
    | exact resolve eq13 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq29 (τ X0) X2 X1
       grind)
    | exact superpose eq29 eq15
    | (have j1 := eq29 (τ X0) X2 X2
       grind)
    | exact resolve eq15 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq29
  have eq53 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22
    | exact resolve eq22 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op (M.op (M.op (M.op (M.op X4 X0) X5) X2) (M.op (M.op X4 X5) X1)) (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq17 (M.op (M.op X4 X0) X5) (M.op (M.op X4 X5) X1) X2 X3
       have i₂ := eq17 X4 X5 X0 X1
       grind)
    | exact superpose eq17 eq17
    | exact resolve eq17 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 (M.op X3 X4)) X1)) = (M.op (M.op (M.op X3 X2) X4) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq17 X3 X4 X2 (M.op (M.op X0 (M.op X3 X4)) X1)
       have i₂ := eq8 X0 X1 (M.op X3 X4)
       grind)
    | exact superpose eq8 eq17
    | exact resolve eq17 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op (M.op X2 X3) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X2 X0) (M.op (M.op X2 X3) X1) X3
       have i₂ := eq17 X2 X3 X0 X1
       grind)
    | exact superpose eq17 eq8
    | exact resolve eq8 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X0) X3) X4) = (M.op (M.op (M.op X2 X3) X1) (M.op (M.op X0 X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op (M.op X2 X0) X3) X4 (M.op (M.op X2 X3) X1)
       have i₂ := eq17 X2 X3 X0 X1
       grind)
    | exact superpose eq17 eq8
    | exact resolve eq8 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op (M.op X0 X1) (M.op (M.op (M.op X4 X0) X5) (M.op (M.op X4 X5) X1))) X3)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq73 X0 X1 X2 X3 X4 X5
       have i₂ := eq75 (M.op X0 X1) X3 X2 (M.op (M.op X4 X0) X5) (M.op (M.op X4 X5) X1)
       grind)
    | exact superpose eq75 eq73
    | exact resolve eq73 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq91 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq83 X0 X1 X2 X3 x x
       have i₂ := eq17 x x X0 X1
       grind)
    | exact superpose eq17 eq83
    | exact resolve eq83 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq109 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 (M.op X3 X0)) X2) (M.op X4 X5)) = (M.op X3 (M.op (M.op X4 (M.op X0 (M.op X1 X2))) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq18 X4 X5 X3 (M.op (M.op X1 (M.op X3 X0)) X2)
       have i₂ := eq18 X1 X2 X3 X0
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op X0 (M.op X1 X2)) ∨ (k X0 X3) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X1 X2 X0 X0
       have i₂ := eq12 X0 X3
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 X0 X3
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op (M.op X2 X0) X3) X4)) = (M.op (M.op X2 X3) (M.op (M.op X0 X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq18 (M.op (M.op X2 X0) X3) X4 (M.op X2 X3) X1
       have i₂ := eq17 X2 X3 X0 X1
       grind)
    | exact superpose eq17 eq18
    | exact resolve eq18 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 (M.op X3 X0)) X2) X4) = (M.op (M.op (M.op X0 (M.op X1 X2)) X5) (M.op (M.op X3 X5) X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq17 X3 X5 (M.op (M.op X1 (M.op X3 X0)) X2) X4
       have i₂ := eq18 X1 X2 X3 X0
       grind)
    | exact superpose eq18 eq17
    | exact resolve eq17 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X1 (M.op (M.op X4 X5) X0)) X2)) = (M.op (M.op (M.op X4 X3) X5) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq17 X4 X5 X3 (M.op (M.op X1 (M.op (M.op X4 X5) X0)) X2)
       have i₂ := eq18 X1 X2 (M.op X4 X5) X0
       grind)
    | exact superpose eq18 eq17
    | exact resolve eq17 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X1 (M.op (M.op X4 X5) X0)) X2)) = (M.op X3 (M.op (M.op X0 (M.op X4 X5)) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq123 X0 X1 X2 X3 X4 X5
       have i₂ := eq75 X0 (M.op X1 X2) X3 X4 X5
       grind)
    | exact superpose eq75 eq123
    | exact resolve eq123 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq129 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 (M.op X3 X0)) X2) X4) = (M.op (M.op (M.op X0 X3) (M.op X1 X2)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq121 X0 X1 X2 X3 X4 x
       have i₂ := eq81 X3 x X0 (M.op X1 X2) X4
       grind)
    | exact superpose eq81 eq121
    | exact resolve eq121 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq121
  have eq135 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X0 (M.op X1 X2)) ∨ (k X0 X3) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq110 X0 X1 X2 X3
       have i₂ := eq8 X1 X2 X0
       grind)
    | exact superpose eq8 eq110
    | (have j0 := eq110 X0 X1 X2 X3
       grind)
    | exact resolve eq110 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq136 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X4 (M.op X0 (M.op X1 X2))) X5)) = (M.op (M.op X3 X0) (M.op (M.op X4 (M.op X1 X2)) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq109 X0 X1 X2 X3 X4 X5
       have i₂ := eq75 X4 X5 (M.op X3 X0) X1 X2
       grind)
    | exact superpose eq75 eq109
    | exact resolve eq109 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq220 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq27 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq588 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq31
    | (have j0 := eq31 X1 X1
       grind)
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq635 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq588 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq588
    | (have j0 := eq588 X0 X1
       grind)
    | exact resolve eq588 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq1183 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X2) X1) (M.op X3 X4)) = (M.op (M.op X2 X3) (M.op (M.op X0 X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq78 X3 X4 X2 (M.op (M.op X0 X2) X1)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq78
    | exact resolve eq78 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1217 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X2 (M.op X0 X1)
       have i₂ := eq78 X1 X2 X0 (M.op X0 X1)
       grind)
    | exact superpose eq78 eq8
    | exact resolve eq8 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1218 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X1) X4)) = (M.op (M.op X3 X0) (M.op (M.op X0 (M.op X1 X2)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq18 (M.op X3 X1) X4 (M.op X3 X0) X2
       have i₂ := eq78 X1 X2 X3 X0
       grind)
    | exact superpose eq78 eq18
    | exact resolve eq18 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1220 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op (M.op (M.op X3 X0) X2) (M.op (M.op X0 (M.op X1 X2)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op X3 X1) X4 (M.op (M.op X3 X0) X2)
       have i₂ := eq78 X1 X2 X3 X0
       grind)
    | exact superpose eq78 eq8
    | exact resolve eq8 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq1233 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op X0 (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X2)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1220 X0 X1 X2 X3 X4
       have i₂ := eq75 (M.op X0 (M.op X1 X2)) X4 X0 X3 X2
       grind)
    | exact superpose eq75 eq1220
    | exact resolve eq1220 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220
  have eq1235 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X1) X4)) = (M.op X3 (M.op (M.op X0 (M.op X0 (M.op X1 X2))) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1218 X0 X1 X2 X3 X4
       have i₂ := eq136 X0 X1 X2 X3 X0 X4
       grind)
    | exact superpose eq136 eq1218
    | exact resolve eq1218 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq1218
  have eq1250 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 (M.op X0 X1)) X4)) = (M.op (M.op X2 X3) (M.op (M.op X0 X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1183 X0 X1 X2 X3 X4
       have i₂ := eq75 X3 X4 X2 X0 X1
       grind)
    | exact superpose eq75 eq1183
    | exact resolve eq1183 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq1183
  have eq1258 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op X0 (M.op (M.op (M.op X2 X1) (M.op X0 (M.op X3 X2))) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1233 X0 X1 X2 X3 X4
       have i₂ := eq129 X2 X0 (M.op X3 X2) X1 X4
       grind)
    | (have i₁ := eq1233 X0 X1 X2 X1 X4
       have i₂ := eq129 X0 X1 X2 (M.op X1 X2) X4
       grind)
    | exact superpose eq129 eq1233
    | exact resolve eq1233 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq1233
  have eq1268 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op (M.op X3 X2) (M.op (M.op X2 X1) X4)) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq1258 x X1 X2 X3 X4
       have i₂ := eq18 (M.op X2 X1) X4 x (M.op X3 X2)
       grind)
    | exact superpose eq18 eq1258
    | exact resolve eq1258 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258
  have eq1273 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op X3 (M.op (M.op X2 (M.op X2 X1)) X4)) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq1268 X1 X2 X3 X4
       have i₂ := eq1250 X2 X1 X3 X2 X4
       grind)
    | (have i₁ := eq1268 (M.op x X1) X3 X3 X4
       have i₂ := eq1250 x X1 (M.op X3 X3) X3 X4
       grind)
    | exact superpose eq1250 eq1268
    | exact resolve eq1268 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268
  have eq1288 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X0) X3) X4) = (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1217 (M.op (M.op X2 X0) X3) (M.op (M.op X2 X3) X1) X4
       have i₂ := eq17 X2 X3 X0 X1
       grind)
    | exact superpose eq17 eq1217
    | exact resolve eq1217 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1290 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op (M.op X2 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1217 (M.op X0 X2) (M.op X2 X1) X3
       have i₂ := eq1217 X0 X2 X1
       grind)
    | exact superpose eq1217 eq1217
    | exact resolve eq1217 eq1217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1293 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X3) X1)) = (M.op (M.op X2 X3) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1217 X2 X3 (M.op (M.op X0 X3) X1)
       have i₂ := eq8 X0 X1 X3
       grind)
    | exact superpose eq8 eq1217
    | exact resolve eq1217 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1312 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X0 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X0 X1) X0
       have i₂ := eq1217 X2 X0 X1
       grind)
    | exact superpose eq1217 eq8
    | exact resolve eq8 eq1217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1315 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) X3)) = (M.op X2 (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 (M.op X0 X1) X3 X1 X2
       have i₂ := eq1217 X0 X1 X2
       grind)
    | exact superpose eq1217 eq18
    | exact resolve eq18 eq1217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1316 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0) X1
       have i₂ := eq1217 X0 X0 X0
       grind)
    | exact superpose eq1217 eq11
    | (have j0 := eq11 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq11 (M.op x x) X1
       have r₂ := eq1217 x x x
       grind)
    | exact resolve eq11 eq1217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1319 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X1) X3) = (M.op (M.op (M.op X0 X1) X4) (M.op (M.op (M.op X0 X2) X4) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq17 (M.op X0 X2) X4 (M.op X2 X1) X3
       have i₂ := eq1217 X0 X2 X1
       grind)
    | exact superpose eq1217 eq17
    | exact resolve eq17 eq1217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1327 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1316 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316
  have eq1331 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X1) X3) = (M.op (M.op X0 X4) (M.op (M.op X2 (M.op (M.op X0 X1) X4)) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1319 X0 X1 X2 X3 X4
       have i₂ := eq115 X2 (M.op (M.op X0 X1) X4) X0 X4 X3
       grind)
    | (have i₁ := eq1319 X0 X1 X2 X4 X1
       have i₂ := eq115 (M.op X0 X2) X1 (M.op X0 X1) X1 X4
       grind)
    | exact superpose eq115 eq1319
    | exact resolve eq1319 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq1319
  have eq1343 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op X1 (M.op (M.op X2 (M.op X0 X1)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1290 X0 X1 X2 X3
       have i₂ := eq1315 X2 (M.op X0 X1) X1 X3
       grind)
    | (have i₁ := eq1290 X0 X1 X2 X3
       have i₂ := eq1315 X2 X1 (M.op X0 X1) X3
       grind)
    | exact superpose eq1315 eq1290
    | exact resolve eq1290 eq1315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290
  have eq1345 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X0) X3) X4) = (M.op X1 (M.op (M.op (M.op X2 X3) (M.op X0 X1)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1288 X0 X1 X2 X3 X4
       have i₂ := eq1315 (M.op X2 X3) (M.op X0 X1) X1 X4
       grind)
    | (have i₁ := eq1288 X0 X1 X2 X3 X4
       have i₂ := eq1315 (M.op X2 X3) X1 (M.op X0 X1) X4
       grind)
    | exact superpose eq1315 eq1288
    | exact resolve eq1288 eq1315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288
  have eq1353 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X1) X3) = (M.op (M.op X0 X4) (M.op (M.op X4 (M.op X0 X1)) (M.op X2 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1331 X0 X1 X2 X3 X4
       have i₂ := eq127 X4 X2 X3 (M.op X0 X4) X0 X1
       grind)
    | (have i₁ := eq1331 X0 X1 X0 (M.op X1 X2) x
       have i₂ := eq127 X0 X1 X2 (M.op X0 x) (M.op X0 X1) x
       grind)
    | exact superpose eq127 eq1331
    | exact resolve eq1331 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq1331
  have eq1360 : ∀ X0 X2 X3 X4 : G, (M.op (M.op (M.op X2 X0) X3) X4) = (M.op (M.op X0 (M.op X2 X3)) X4) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq1345 X0 x X2 X3 X4
       have i₂ := eq1343 X0 x (M.op X2 X3) X4
       grind)
    | exact superpose eq1343 eq1345
    | exact resolve eq1345 eq1343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1343 eq1345
  have eq1367 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X1) X3) = (M.op X0 (M.op (M.op X4 (M.op X4 (M.op X0 X1))) (M.op X2 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1353 X0 X1 X2 X3 X4
       have i₂ := eq1250 X4 (M.op X0 X1) X0 X4 (M.op X2 X3)
       grind)
    | (have i₁ := eq1353 X0 X1 X2 X3 X3
       have i₂ := eq1250 X0 X1 (M.op X0 X3) X3 (M.op X2 X3)
       grind)
    | exact superpose eq1250 eq1353
    | exact resolve eq1353 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250 eq1353
  have eq1373 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X3) = (M.op X1 (M.op (M.op X0 X0) (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1367 X0 X1 X2 X3 x
       have i₂ := eq1235 x X0 X1 X0 (M.op X2 X3)
       grind)
    | exact superpose eq1235 eq1367
    | exact resolve eq1367 eq1235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1235 eq1367
  have eq1378 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X3) = (M.op X1 (M.op X0 (M.op (M.op X2 X0) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1373 X0 X1 X2 X3
       have i₂ := eq1293 X2 X3 X0 X0
       grind)
    | (have i₁ := eq1373 X0 X1 (M.op X0 X3) X1
       have i₂ := eq1293 X0 X1 (M.op X0 X0) X3
       grind)
    | exact superpose eq1293 eq1373
    | exact resolve eq1373 eq1293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293 eq1373
  have eq1380 : ∀ X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op (M.op X2 X1) X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq1378 x X1 X2 X3
       have i₂ := eq8 X2 X3 x
       grind)
    | exact superpose eq8 eq1378
    | exact resolve eq1378 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378
  have eq1693 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X1 X1)
       have i₂ := eq1327 X1 (τ X0)
       grind)
    | exact superpose eq1327 eq16
    | exact resolve eq16 eq1327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq1696 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op X1 X1) X0
       have i₂ := eq1327 X1 (σ X0)
       grind)
    | exact superpose eq1327 eq22
    | exact resolve eq22 eq1327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327
  have eq1697 : ∀ X0 X1 : G, (k (τ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1696 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1696
    | exact resolve eq1696 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1696
  have eq1700 : ∀ X0 X1 : G, (k (σ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1693 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1693
    | exact resolve eq1693 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1693
  have eq1798 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (τ (M.op X1 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (τ (M.op X1 X1)) X0
       have i₂ := eq1697 (σ X0) X1
       grind)
    | exact superpose eq1697 eq22
    | exact resolve eq22 eq1697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1697
  have eq1802 : ∀ X0 X1 : G, (k (τ (τ (M.op X1 X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1798 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1798
    | exact resolve eq1798 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1798
  have eq1931 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = X1 ∨ (σ (k X0 X2)) = (σ (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1700 X1 X0
       have i₂ := eq635 X2 X0
       grind)
    | exact superpose eq635 eq1700
    | (have j1 := eq635 X2 X0
       grind)
    | exact resolve eq1700 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635 eq1700
  have eq2129 : ∀ X0 : G, (σ (τ (τ (M.op X0 X0)))) ≠ (σ (τ (τ (M.op X0 X0)))) ∨ (σ (τ (τ (M.op X0 X0)))) = (M.op (σ (τ (τ (M.op X0 X0)))) (σ (τ (τ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq220 (τ (τ (M.op X0 X0)))
       have i₂ := eq1802 (τ (τ (M.op X0 X0))) X0
       grind)
    | exact superpose eq1802 eq220
    | (have j0 := eq220 (τ (τ (M.op X0 X0)))
       grind)
    | exact resolve eq220 eq1802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1802
  have eq2143 : ∀ X0 : G, (σ (τ (τ (M.op X0 X0)))) = (M.op (σ (τ (τ (M.op X0 X0)))) (σ (τ (τ (M.op X0 X0))))) := by
    intro X0
    first
    | (have j0 := eq2129 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2129
  have eq2151 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2143 X0
       have i₂ := eq10 (τ (M.op X0 X0))
       grind)
    | exact superpose eq10 eq2143
    | exact resolve eq2143 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2143
  have eq2207 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq48 x y X0
       grind)
    | exact superpose eq48 eq14
    | (have j1 := eq48 x x X0
       grind)
    | exact resolve eq14 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq2269 : ∀ X0 : G, (k (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2207 X0
       have j1 := eq1931 x X0 x
       grind)
    | (have r₁ := eq2207 X0
       have r₂ := eq1931 x x y
       grind)
    | exact resolve eq2207 eq1931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1931 eq2207
  have eq2322 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq22 (σ x) X0
       have i₂ := eq2269 (σ X0)
       grind)
    | exact superpose eq2269 eq22
    | exact resolve eq22 eq2269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269
  have eq2326 : ∀ X0 : G, (τ (σ X0)) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq2322 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq2322
    | exact resolve eq2322 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2322
  have eq2335 : ∀ X0 : G, (k x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2326 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2326
    | exact resolve eq2326 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2326
  have eq2344 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op (τ X0) X1)) = (k X0 (σ (M.op (M.op (M.op X2 X3) (M.op X2 X3)) X1))) ∨ (k (τ X0) X4) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 X0 (M.op (M.op (M.op X2 X3) (M.op X2 X3)) X1) X4
       have i₂ := eq91 X2 X3 (τ X0) X1
       grind)
    | exact superpose eq91 eq49
    | (have j0 := eq49 X0 X1 X4
       grind)
    | exact resolve eq49 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq91
  have eq2442 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op (τ X0) X1)) = (k X0 (σ (M.op (M.op X3 (M.op X2 (M.op X2 X3))) X1))) ∨ (k (τ X0) X4) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2344 X0 X1 X2 X3 X4
       have i₂ := eq1360 X3 X2 (M.op X2 X3) X1
       grind)
    | exact superpose eq1360 eq2344
    | (have j0 := eq2344 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq2344 eq1360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1360 eq2344
  have eq2451 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op (τ X0) X1)) = (k X0 (σ (M.op (M.op X2 (M.op X2 X3)) (M.op X3 X1)))) ∨ (k (τ X0) X4) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2442 X0 X1 X2 X3 X4
       have i₂ := eq1380 (M.op X2 (M.op X2 X3)) X3 X1
       grind)
    | exact superpose eq1380 eq2442
    | (have j0 := eq2442 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq2442 eq1380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2442
  have eq2453 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op (τ X0) X1)) = (k X0 (σ (M.op X3 (M.op (M.op X2 (M.op X2 X3)) X1)))) ∨ (k (τ X0) X4) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2451 X0 X1 X2 X3 X4
       have i₂ := eq1312 X3 X1 (M.op X2 (M.op X2 X3))
       grind)
    | (have i₁ := eq2451 X0 X1 X2 X3 X4
       have i₂ := eq1312 (M.op X2 (M.op X2 X3)) X1 X3
       grind)
    | exact superpose eq1312 eq2451
    | (have j0 := eq2451 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq2451 eq1312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312 eq2451
  have eq2455 : ∀ X0 X1 X3 X4 : G, (σ (M.op (τ X0) X1)) = (k X0 (σ (M.op (M.op X3 X3) X1))) ∨ (k (τ X0) X4) = X4 := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq2453 X0 X1 x X3 X4
       have i₂ := eq1273 X3 x X3 X1
       grind)
    | (have i₁ := eq2453 X0 X1 x (M.op X3 X1) X4
       have i₂ := eq1273 X1 x X3 (M.op (M.op x (M.op x (M.op X3 X1))) X1)
       grind)
    | exact superpose eq1273 eq2453
    | (have j0 := eq2453 X0 X1 x X3 X4
       grind)
    | exact resolve eq2453 eq1273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2453
  have eq2456 : ∀ X0 X1 X3 X4 : G, (σ (M.op (τ X0) X1)) = (k X0 (σ (M.op X3 (M.op X3 X1)))) ∨ (k (τ X0) X4) = X4 := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq2455 X0 X1 X3 X4
       have i₂ := eq1380 X3 X3 X1
       grind)
    | exact superpose eq1380 eq2455
    | (have j0 := eq2455 X0 X1 X3 X4
       grind)
    | exact resolve eq2455 eq1380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2455
  have eq2465 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq220 x
       have i₂ := eq2335 x
       grind)
    | exact superpose eq2335 eq220
    | (have j0 := eq220 x
       grind)
    | exact resolve eq220 eq2335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2477 : ∀ X0 : G, (τ (σ X0)) = (k (τ x) X0) := by
    intro X0
    first
    | (have i₁ := eq22 x X0
       have i₂ := eq2335 (σ X0)
       grind)
    | exact superpose eq2335 eq22
    | exact resolve eq22 eq2335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2335
  have eq2479 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2465
  have eq2481 : ∀ X0 : G, (k (τ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2477 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2477
    | exact resolve eq2477 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2477
  have eq2856 : (σ (τ x)) ≠ (σ (τ x)) ∨ (σ (τ x)) = (M.op (σ (τ x)) (σ (τ x))) := by
    first
    | (have i₁ := eq220 (τ x)
       have i₂ := eq2481 (τ x)
       grind)
    | exact superpose eq2481 eq220
    | (have j0 := eq220 (τ x)
       grind)
    | exact resolve eq220 eq2481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq2481
  have eq2871 : (σ (τ x)) = (M.op (σ (τ x)) (σ (τ x))) := by grind
  clear eq2856
  have eq2879 : x = (M.op x x) := by
    first
    | (have i₁ := eq2871
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2871
    | exact resolve eq2871 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2871
  have eq3083 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op x X1) (M.op (M.op x X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 x X1 x X0
       have i₂ := eq2879
       grind)
    | exact superpose eq2879 eq17
    | exact resolve eq17 eq2879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq3084 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op x (M.op (M.op X0 x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 x x
       have i₂ := eq2879
       grind)
    | exact superpose eq2879 eq18
    | exact resolve eq18 eq2879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2879
  have eq3100 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3084 X0 X1
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq3084
    | exact resolve eq3084 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3084
  have eq3101 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op (M.op x (M.op x X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3083 X0 X1
       have i₂ := eq1315 x (M.op x X1) X1 X0
       grind)
    | (have i₁ := eq3083 X0 X1
       have i₂ := eq1315 x X1 (M.op x X1) X0
       grind)
    | exact superpose eq1315 eq3083
    | exact resolve eq3083 eq1315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315 eq3083
  have eq3105 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3101 X0 X1
       have i₂ := eq1273 X1 x X1 X0
       grind)
    | (have i₁ := eq3101 X0 (M.op x X1)
       have i₂ := eq1273 X1 x x (M.op (M.op x (M.op x (M.op x X1))) X0)
       grind)
    | exact superpose eq1273 eq3101
    | exact resolve eq3101 eq1273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1273 eq3101
  have eq3107 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3105 X0 X1
       have i₂ := eq1380 X1 X1 X0
       grind)
    | exact superpose eq1380 eq3105
    | exact resolve eq3105 eq1380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1380 eq3105
  have eq4547 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq1217 (σ x) (σ x) X0
       have i₂ := eq2479
       grind)
    | exact superpose eq2479 eq1217
    | exact resolve eq1217 eq2479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217 eq2479
  have eq4552 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq4547 X0
       have i₂ := eq3107 X0 (σ x)
       grind)
    | exact superpose eq3107 eq4547
    | exact resolve eq4547 eq3107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4547
  have eq7487 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq4552 (σ y)
       grind)
    | exact superpose eq4552 eq14
    | exact resolve eq14 eq4552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4552
  have eq303590 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (M.op x (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3107 (τ (M.op X0 X0)) (τ (M.op X0 X0))
       have i₂ := eq2151 X0
       grind)
    | exact superpose eq2151 eq3107
    | exact resolve eq3107 eq2151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303608 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op x (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq303590 X0
       have i₂ := eq2151 X0
       grind)
    | exact superpose eq2151 eq303590
    | exact resolve eq303590 eq2151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2151 eq303590
  have eq315652 : ∀ X0 X1 X2 X3 : G, (k X0 X1) = X1 ∨ (σ (M.op X0 X2)) = (k (σ X0) (σ (M.op X3 (M.op X3 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2456 (σ X0) X1 X3 x
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2456
    | exact resolve eq2456 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2456
  have eq315672 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 X2)) = (σ (k X0 (M.op X3 (M.op X3 X2)))) ∨ (k X0 X1) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq315652 X0 X1 X2 X3
       have i₂ := eq13 X0 (M.op X3 (M.op X3 X2))
       grind)
    | exact superpose eq13 eq315652
    | (have j0 := eq315652 X0 X1 X2 X3
       grind)
    | exact resolve eq315652 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315652
  have eq315698 : ∀ X0 X1 X2 : G, (σ (M.op X0 X2)) = (σ (k X0 (M.op x X2))) ∨ (k X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq315672 X0 X1 X2 x
       have i₂ := eq3107 X2 x
       grind)
    | exact superpose eq3107 eq315672
    | (have j0 := eq315672 X0 X1 X2 x
       grind)
    | exact resolve eq315672 eq3107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315672
  have eq402742 : ∀ X0 X1 X2 : G, (τ (σ (M.op X0 X1))) = (k X0 (M.op x X1)) ∨ (k X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (k X0 (M.op x X1))
       have i₂ := eq315698 X0 X2 X1
       grind)
    | exact superpose eq315698 eq9
    | (have j1 := eq315698 X0 X2 X2
       grind)
    | exact resolve eq9 eq315698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315698
  have eq402757 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 (M.op x X1)) ∨ (k X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq402742 X0 X1 X2
       have i₂ := eq9 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq402742
    | (have j0 := eq402742 X0 X1 X2
       grind)
    | exact resolve eq402742 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402742
  have eq402916 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op x X1) ∨ (M.op X0 X1) = (k X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have j0 := eq402757 X0 X1 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402757
  have eq414207 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 (M.op X0 X1)) ∨ (M.op X2 (M.op X0 X1)) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq402916 X0 (M.op X0 X1)
       have i₂ := eq3100 X0 X1
       grind)
    | exact superpose eq3100 eq402916
    | exact resolve eq402916 eq3100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3100 eq402916
  have eq414252 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq414207 X0 X1 X2
       have j1 := eq135 X2 X1 X2 (M.op X0 X1)
       grind)
    | (have r₁ := eq414207 X1 X2 X0
       have r₂ := eq135 X0 X1 X2 x
       grind)
    | exact resolve eq414207 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq414207
  have eq424529 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq414252 X0 X0 X2
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq414252
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq414252 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq424787 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq414252 x (τ (M.op X0 X0)) x
       have i₂ := eq303608 X0
       grind)
    | exact superpose eq303608 eq414252
    | exact resolve eq414252 eq303608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303608
  have eq452593 : ∀ X0 X1 : G, (M.op (τ X0) (τ (M.op X1 X1))) = (τ (k X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op X1 X1) X0
       have i₂ := eq424787 X1 (τ X0)
       grind)
    | exact superpose eq424787 eq53
    | exact resolve eq53 eq424787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424787
  have eq452663 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X1 X1))) = (M.op (τ X0) (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq452593 X0 X1
       have i₂ := eq414252 X1 X1 X0
       grind)
    | exact superpose eq414252 eq452593
    | exact resolve eq452593 eq414252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414252 eq452593
  have eq492892 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq424529 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424529
  have eq492893 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq492892 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492892
  have eq493545 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq53 X0 X0
       have i₂ := eq492893 (τ X0)
       grind)
    | exact superpose eq492893 eq53
    | exact resolve eq53 eq492893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq493635 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq493545 X0
       have i₂ := eq492893 X0
       grind)
    | exact superpose eq492893 eq493545
    | exact resolve eq493545 eq492893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492893 eq493545
  have eq494143 : ∀ X0 : G, (M.op x (τ X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3107 (τ X0) (τ X0)
       have i₂ := eq493635 X0
       grind)
    | exact superpose eq493635 eq3107
    | exact resolve eq3107 eq493635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493635
  have eq494186 : ∀ X0 : G, (M.op x (τ X0)) = (τ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq494143 X0
       have i₂ := eq452663 X0 X0
       grind)
    | exact superpose eq452663 eq494143
    | exact resolve eq494143 eq452663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452663 eq494143
  have eq494349 : ∀ X0 : G, (M.op x (τ X0)) = (τ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq494186 X0
       have i₂ := eq3107 X0 X0
       grind)
    | exact superpose eq3107 eq494186
    | exact resolve eq494186 eq3107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3107 eq494186
  have eq494794 : ∀ X0 : G, (M.op x X0) = (σ (M.op x (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op x X0)
       have i₂ := eq494349 X0
       grind)
    | exact superpose eq494349 eq10
    | exact resolve eq10 eq494349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494349
  have eq495545 : ∀ X0 : G, (σ (M.op x X0)) = (M.op x (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq494794 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq494794
    | exact resolve eq494794 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494794
  have eq496278 : (M.op x (σ y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq7487
       have i₂ := eq495545 y
       grind)
    | exact superpose eq495545 eq7487
    | (have r₁ := eq7487
       have r₂ := eq495545 y
       grind)
    | exact resolve eq7487 eq495545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7487 eq495545
  have eq496421 : False := by grind
  exact eq496421

/-- `Equation3591`: `x ◇ y = z ◇ ((x ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pxx_pyx_Equation3591 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3591 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3591.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X2) X1)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X0 X2) X1) (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op (M.op X0 X2) X1)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 (M.op X2 X3)) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op (M.op X0 (M.op X2 X3)) X1) X3
       have i₂ := eq8 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k X0 (τ X1)) X2
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq13
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq41 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X2) = (k X2 X0) := by
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
  have eq43 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 X0 (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq41 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq83 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq103 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op (M.op X0 X2) X1)) ∨ (k X3 X0) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X0 X2 X0 X1
       have i₂ := eq12 X3 X0
       grind)
    | exact superpose eq12 eq21
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op (M.op (M.op (M.op (M.op X4 X0) X5) X2) (M.op (M.op X4 X5) X1)) (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq21 (M.op (M.op X4 X0) X5) (M.op (M.op X4 X5) X1) X2 X3
       have i₂ := eq21 X4 X5 X0 X1
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 (M.op X3 X4)) X1)) = (M.op (M.op (M.op X3 X2) X4) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq21 X3 X4 X2 (M.op (M.op X0 (M.op X3 X4)) X1)
       have i₂ := eq8 X0 X1 (M.op X3 X4)
       grind)
    | exact superpose eq8 eq21
    | exact resolve eq21 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op (M.op X2 X3) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X2 X0) (M.op (M.op X2 X3) X1) X3
       have i₂ := eq21 X2 X3 X0 X1
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X0) X3) X4) = (M.op (M.op (M.op X2 X3) X1) (M.op (M.op X0 X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op (M.op X2 X0) X3) X4 (M.op (M.op X2 X3) X1)
       have i₂ := eq21 X2 X3 X0 X1
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op (M.op X0 X1) (M.op (M.op (M.op X4 X0) X5) (M.op (M.op X4 X5) X1))) X3)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq112 X0 X1 X2 X3 X4 X5
       have i₂ := eq114 (M.op X0 X1) X3 X2 (M.op (M.op X4 X0) X5) (M.op (M.op X4 X5) X1)
       grind)
    | exact superpose eq114 eq112
    | exact resolve eq112 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq133 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op X2 X1)) ∨ (k X3 X0) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq103 X0 X1 X2 X3
       have i₂ := eq119 X2 X1 X0 X2
       grind)
    | exact superpose eq119 eq103
    | (have j0 := eq103 X0 X1 X2 X3
       grind)
    | exact resolve eq103 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq134 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq125 X0 X1 X2 X3 x x
       have i₂ := eq21 x x X0 X1
       grind)
    | exact superpose eq21 eq125
    | exact resolve eq125 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq142 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq83 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 (M.op X3 X0)) X2) (M.op X4 X5)) = (M.op X3 (M.op (M.op X4 (M.op X0 (M.op X1 X2))) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq22 X4 X5 X3 (M.op (M.op X1 (M.op X3 X0)) X2)
       have i₂ := eq22 X1 X2 X3 X0
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op (M.op X2 X0) X3) X4)) = (M.op (M.op X2 X3) (M.op (M.op X0 X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq22 (M.op (M.op X2 X0) X3) X4 (M.op X2 X3) X1
       have i₂ := eq21 X2 X3 X0 X1
       grind)
    | exact superpose eq21 eq22
    | exact resolve eq22 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 (M.op X3 X0)) X2) X4) = (M.op (M.op (M.op X0 (M.op X1 X2)) X5) (M.op (M.op X3 X5) X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq21 X3 X5 (M.op (M.op X1 (M.op X3 X0)) X2) X4
       have i₂ := eq22 X1 X2 X3 X0
       grind)
    | exact superpose eq22 eq21
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X1 (M.op (M.op X4 X5) X0)) X2)) = (M.op (M.op (M.op X4 X3) X5) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq21 X4 X5 X3 (M.op (M.op X1 (M.op (M.op X4 X5) X0)) X2)
       have i₂ := eq22 X1 X2 (M.op X4 X5) X0
       grind)
    | exact superpose eq22 eq21
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X1 (M.op (M.op X4 X5) X0)) X2)) = (M.op X3 (M.op (M.op X0 (M.op X4 X5)) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq166 X0 X1 X2 X3 X4 X5
       have i₂ := eq114 X0 (M.op X1 X2) X3 X4 X5
       grind)
    | exact superpose eq114 eq166
    | exact resolve eq166 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq172 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 (M.op X3 X0)) X2) X4) = (M.op (M.op (M.op X0 X3) (M.op X1 X2)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq164 X0 X1 X2 X3 X4 x
       have i₂ := eq120 X3 x X0 (M.op X1 X2) X4
       grind)
    | exact superpose eq120 eq164
    | exact resolve eq164 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq180 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X4 (M.op X0 (M.op X1 X2))) X5)) = (M.op (M.op X3 X0) (M.op (M.op X4 (M.op X1 X2)) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq149 X0 X1 X2 X3 X4 X5
       have i₂ := eq114 X4 X5 (M.op X3 X0) X1 X2
       grind)
    | exact superpose eq114 eq149
    | exact resolve eq149 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq187 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq142 (σ X0)
       grind)
    | exact superpose eq142 eq13
    | exact resolve eq13 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq142 (τ X0)
       grind)
    | exact superpose eq142 eq31
    | exact resolve eq31 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq196 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq189 X0
       have i₂ := eq142 X0
       grind)
    | exact superpose eq142 eq189
    | exact resolve eq189 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq198 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq187 X0
       have i₂ := eq142 X0
       grind)
    | exact superpose eq142 eq187
    | exact resolve eq187 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq250 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op (τ X0) (M.op (τ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (τ X0) X1 (τ X0)
       have i₂ := eq196 X0
       grind)
    | exact superpose eq196 eq8
    | exact resolve eq8 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq43 x y
       grind)
    | exact superpose eq43 eq14
    | (have j1 := eq43 x x
       grind)
    | exact resolve eq14 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq285 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ X0)
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq11
    | (have j0 := eq11 X1 (σ X0)
       have j1 := eq43 X0 X1
       grind)
    | (have r₁ := eq11 X0 (σ X0)
       have r₂ := eq43 X0 X1
       grind)
    | exact resolve eq11 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq303 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq285 X0 X1
       have j1 := eq11 X1 (σ X0)
       grind)
    | (have r₁ := eq285 X0 X1
       have r₂ := eq11 X0 (σ X0)
       grind)
    | exact resolve eq285 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq310 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq275
       have i₂ := eq198 x
       grind)
    | exact superpose eq198 eq275
    | exact resolve eq275 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq320 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq303 X0 X1
       have i₂ := eq142 X0
       grind)
    | exact superpose eq142 eq303
    | (have j0 := eq303 X0 X1
       grind)
    | exact resolve eq303 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq303
  have eq513 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (τ (M.op X0 X0)) X1) X2) = (M.op (M.op (M.op (τ X0) X1) X3) (M.op (M.op (τ X0) X3) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 (τ X0) X3 (M.op (τ (M.op X0 X0)) X1) X2
       have i₂ := eq250 X0 X1
       grind)
    | exact superpose eq250 eq21
    | exact resolve eq21 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq519 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (τ (M.op X0 X0)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq513 X0 X1 X2 x
       have i₂ := eq21 (τ X0) x X1 X2
       grind)
    | exact superpose eq21 eq513
    | exact resolve eq513 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq577 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (τ (σ (M.op X0 X0))) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq519 (σ X0) X1 X2
       have i₂ := eq198 X0
       grind)
    | exact superpose eq198 eq519
    | exact resolve eq519 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq582 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X3) = (M.op (M.op (M.op X0 (τ (M.op X2 X2))) X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq519 X2 (M.op (M.op X0 (τ (M.op X2 X2))) X1) X3
       have i₂ := eq8 X0 X1 (τ (M.op X2 X2))
       grind)
    | exact superpose eq8 eq519
    | exact resolve eq519 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq600 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X2) = (M.op (M.op (M.op X0 X1) X4) (M.op (M.op (M.op (τ (M.op X3 X3)) X0) X4) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq21 (M.op (τ (M.op X3 X3)) X0) X4 X1 X2
       have i₂ := eq519 X3 X0 X1
       grind)
    | exact superpose eq519 eq21
    | exact resolve eq21 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq627 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op (M.op X0 (M.op (τ (M.op X3 X3)) X0)) X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq600 X0 X1 X2 X3 x
       have i₂ := eq120 (M.op (τ (M.op X3 X3)) X0) x X0 X1 X2
       grind)
    | exact superpose eq120 eq600
    | exact resolve eq600 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq600
  have eq640 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq577 X0 X1 X2
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq577
    | exact resolve eq577 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq644 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op (M.op X0 (τ (M.op X3 X3))) (M.op X0 X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq627 X0 X1 X2 X3
       have i₂ := eq172 X0 X0 X1 (τ (M.op X3 X3)) X2
       grind)
    | (have i₁ := eq627 X0 (M.op X1 X2) x X3
       have i₂ := eq172 X0 X1 X2 (M.op (τ (M.op X3 X3)) X0) x
       grind)
    | exact superpose eq172 eq627
    | exact resolve eq627 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq627
  have eq651 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq644 X0 X1 X2 x
       have i₂ := eq582 X0 (M.op X0 X1) x X2
       grind)
    | exact superpose eq582 eq644
    | exact resolve eq644 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582 eq644
  have eq719 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op (M.op (M.op (M.op X3 X3) X2) X0) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 (M.op X3 X3) X0 X2 X1
       have i₂ := eq640 X3 X0 X1
       grind)
    | exact superpose eq640 eq21
    | exact resolve eq21 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq720 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) = (M.op (M.op X0 X1) (M.op (M.op (M.op X3 X3) X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 (M.op X3 X3) X1 X0 X2
       have i₂ := eq640 X3 X0 X1
       grind)
    | exact superpose eq640 eq21
    | exact resolve eq21 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq721 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X2 X2) X1 X0
       have i₂ := eq640 X2 X0 X1
       grind)
    | exact superpose eq640 eq8
    | exact resolve eq8 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq758 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) = (M.op X1 (M.op (M.op (M.op X0 (M.op X3 X3)) X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq720 X0 X1 X2 X3
       have i₂ := eq157 (M.op X3 X3) X1 X0 X1 X2
       grind)
    | exact superpose eq157 eq720
    | exact resolve eq720 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq720
  have eq759 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X0 (M.op (M.op X3 X3) X0)) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq719 X0 X1 X2 X3
       have i₂ := eq114 X0 X1 X2 (M.op X3 X3) X0
       grind)
    | exact superpose eq114 eq719
    | exact resolve eq719 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq781 : ∀ X0 X2 X3 : G, (M.op X0 X2) = (M.op (M.op X0 (M.op X3 X3)) X2) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq758 X0 x X2 X3
       have i₂ := eq8 (M.op X0 (M.op X3 X3)) X2 x
       grind)
    | exact superpose eq8 eq758
    | exact resolve eq758 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq782 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X0 (M.op X3 X3)) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq759 X0 X1 X2 X3
       have i₂ := eq170 X0 X0 X1 X2 X3 X3
       grind)
    | (have i₁ := eq759 x (M.op X1 X2) X3 X3
       have i₂ := eq170 x X1 X2 X3 (M.op X3 X3) x
       grind)
    | exact superpose eq170 eq759
    | exact resolve eq759 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq791 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq782 X0 X1 X2 x
       have i₂ := eq781 X0 (M.op X0 X1) x
       grind)
    | exact superpose eq781 eq782
    | exact resolve eq782 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq840 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X2) X1) X3) = (M.op (M.op X2 (M.op X0 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq651 X2 (M.op (M.op X0 X2) X1) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq651
    | exact resolve eq651 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq876 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X0 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X2 X1 X2 X0
       have i₂ := eq651 X2 X0 X1
       grind)
    | exact superpose eq651 eq22
    | exact resolve eq22 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq877 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op (M.op X1 (M.op (M.op X1 X2) X0)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X1 (M.op (M.op X1 X2) X0) X2 X3
       have i₂ := eq651 (M.op X1 X2) X0 (M.op (M.op X1 (M.op (M.op X1 X2) X0)) X3)
       grind)
    | exact superpose eq651 eq21
    | exact resolve eq21 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq921 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op (M.op X0 (M.op X1 X2)) (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq877 X0 X1 X2 X3
       have i₂ := eq170 X0 X1 X3 X0 X1 X2
       grind)
    | (have i₁ := eq877 x X0 X2 (M.op X1 X2)
       have i₂ := eq170 X0 X1 X2 x (M.op X0 X2) x
       grind)
    | exact superpose eq170 eq877
    | exact resolve eq877 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877
  have eq954 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op X1 (M.op (M.op X0 (M.op X1 X2)) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq921 X0 X1 X2 X3
       have i₂ := eq876 X1 X3 (M.op X0 (M.op X1 X2))
       grind)
    | (have i₁ := eq921 X0 X1 X2 X3
       have i₂ := eq876 (M.op X0 (M.op X1 X2)) X3 X1
       grind)
    | exact superpose eq876 eq921
    | exact resolve eq921 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq970 : ∀ X0 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op X2 (M.op X0 X3))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq954 X0 x X2 X3
       have i₂ := eq22 X0 X3 x X2
       grind)
    | exact superpose eq22 eq954
    | exact resolve eq954 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq1130 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq721 X0 X1 x
       have i₂ := eq721 X2 X1 x
       grind)
    | exact superpose eq721 eq721
    | exact resolve eq721 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1174 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X1)) ≠ (M.op X0 (M.op X0 (M.op X1 X1))) ∨ (M.op X2 (M.op X1 X1)) = (k (M.op X1 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq83 (M.op X1 X1) X2
       have i₂ := eq721 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq721 eq83
    | (have j0 := eq83 (M.op X1 X1) X2
       grind)
    | exact resolve eq83 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq1180 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op (M.op (M.op (M.op X4 X4) X2) X1) (M.op (M.op X0 (M.op X0 X1)) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq21 (M.op X4 X4) X1 X2 X3
       have i₂ := eq721 X0 X1 X4
       grind)
    | exact superpose eq721 eq21
    | exact resolve eq21 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq1193 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 X2)) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X3 (M.op X2 X2)
       have i₂ := eq721 X0 (M.op (M.op X1 (M.op X2 X2)) X3) X2
       grind)
    | exact superpose eq721 eq8
    | exact resolve eq8 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1200 : ∀ X0 X1 X3 : G, (M.op X1 X3) = (M.op X0 (M.op X0 (M.op X1 X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1193 X0 X1 x X3
       have i₂ := eq781 X1 X3 x
       grind)
    | exact superpose eq781 eq1193
    | exact resolve eq1193 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781 eq1193
  have eq1209 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X4 X4) X1)) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1180 X0 X1 X2 X3 X4
       have i₂ := eq114 (M.op X0 (M.op X0 X1)) X3 X2 (M.op X4 X4) X1
       grind)
    | exact superpose eq114 eq1180
    | exact resolve eq1180 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq1180
  have eq1212 : ∀ X1 X2 : G, (M.op X2 (M.op X1 X1)) = (k (M.op X1 X1) X2) := by
    intro X1 X2
    first
    | (have j0 := eq1174 x X1 X2
       have j1 := eq133 X2 X1 X2 (M.op X1 X1)
       grind)
    | (have r₁ := eq1174 X2 X1 x
       have r₂ := eq133 x (M.op X1 X1) X2 x
       grind)
    | exact resolve eq1174 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq1174
  have eq1262 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op X1 (M.op X4 X4)) (M.op (M.op X0 (M.op X0 X1)) X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1209 X0 X1 X2 X3 X4
       have i₂ := eq170 X1 (M.op X0 (M.op X0 X1)) X3 X2 X4 X4
       grind)
    | (have i₁ := eq1209 X0 x X3 (M.op X1 X2) X4
       have i₂ := eq170 (M.op X0 (M.op X0 x)) X1 X2 X3 (M.op X4 X4) x
       grind)
    | exact superpose eq170 eq1209
    | exact resolve eq1209 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq1289 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op X2 (M.op X1 (M.op (M.op X0 (M.op (M.op X4 X4) (M.op X0 X1))) X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1262 X0 X1 X2 X3 X4
       have i₂ := eq180 (M.op X4 X4) X0 X1 X1 X0 X3
       grind)
    | exact superpose eq180 eq1262
    | exact resolve eq1262 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq1262
  have eq1298 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op X2 (M.op X1 (M.op (M.op (M.op X0 X1) (M.op X4 X4)) (M.op X0 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1289 X0 X1 X2 X3 X4
       have i₂ := eq170 (M.op X0 X1) X0 X3 X1 X4 X4
       grind)
    | (have i₁ := eq1289 X0 X3 X2 (M.op X1 X2) X4
       have i₂ := eq170 X0 X1 X2 X3 (M.op X4 X4) (M.op X0 X3)
       grind)
    | exact superpose eq170 eq1289
    | exact resolve eq1289 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170 eq1289
  have eq1302 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op X2 (M.op X1 (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X4 X4)) X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1298 X0 X1 X2 X3 X4
       have i₂ := eq876 X0 X3 (M.op (M.op X0 X1) (M.op X4 X4))
       grind)
    | (have i₁ := eq1298 X0 X1 X2 X3 X4
       have i₂ := eq876 (M.op (M.op X0 X1) (M.op X4 X4)) X3 X0
       grind)
    | exact superpose eq876 eq1298
    | exact resolve eq1298 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298
  have eq1305 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op X2 (M.op X1 (M.op X0 (M.op (M.op X1 (M.op X0 (M.op X4 X4))) X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1302 X0 X1 X2 X3 X4
       have i₂ := eq840 X0 (M.op X4 X4) X1 X3
       grind)
    | (have i₁ := eq1302 X0 X1 X2 X3 X1
       have i₂ := eq840 X1 X1 (M.op X0 X1) X3
       grind)
    | exact superpose eq840 eq1302
    | exact resolve eq1302 eq840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840 eq1302
  have eq1307 : ∀ X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op X2 (M.op X1 (M.op (M.op X4 X4) (M.op X1 X3)))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq1305 x X1 X2 X3 X4
       have i₂ := eq22 X1 X3 x (M.op X4 X4)
       grind)
    | exact superpose eq22 eq1305
    | exact resolve eq1305 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1305
  have eq1309 : ∀ X2 X3 X4 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op X4 X4) X3)) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq1307 x X2 X3 X4
       have i₂ := eq970 x (M.op X4 X4) X3
       grind)
    | (have i₁ := eq1307 X2 X2 X3 X4
       have i₂ := eq970 x X2 (M.op (M.op X4 X4) (M.op X2 X3))
       grind)
    | exact superpose eq970 eq1307
    | exact resolve eq1307 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970 eq1307
  have eq1355 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X3) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq119 X3 X1 X2 X2
       have i₂ := eq721 X0 X1 X2
       grind)
    | exact superpose eq721 eq119
    | exact resolve eq119 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1375 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op X3 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq721 X3 (M.op (M.op X1 X0) X2) X1
       have i₂ := eq119 X1 X2 X1 X0
       grind)
    | exact superpose eq119 eq721
    | exact resolve eq721 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq1424 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op X0 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1375 X0 X1 X2 x
       have i₂ := eq1200 x (M.op X1 X0) X2
       grind)
    | (have i₁ := eq1375 X0 X1 X2 X1
       have i₂ := eq1200 X0 X1 (M.op X1 (M.op (M.op X1 X0) X2))
       grind)
    | exact superpose eq1200 eq1375
    | exact resolve eq1375 eq1200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375
  have eq1440 : ∀ X1 X2 X3 : G, (M.op (M.op X2 X3) X1) = (M.op X2 (M.op X3 X1)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq1355 x X1 X2 X3
       have i₂ := eq791 x X1 (M.op X2 X3)
       grind)
    | exact superpose eq791 eq1355
    | exact resolve eq1355 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791 eq1355
  have eq2022 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X1 X2) (M.op X1 X2)) X3)) = (M.op (M.op (τ (M.op X4 X4)) X0) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq134 X1 X2 (M.op (τ (M.op X4 X4)) X0) X3
       have i₂ := eq519 X4 X0 (M.op (M.op (M.op X1 X2) (M.op X1 X2)) X3)
       grind)
    | exact superpose eq519 eq134
    | exact resolve eq134 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq2111 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X1 X2) (M.op X1 X2)) X3)) = (M.op X0 (M.op (τ (M.op X4 X4)) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2022 X0 X1 X2 X3 X4
       have i₂ := eq1424 X0 (τ (M.op X4 X4)) X3
       grind)
    | exact superpose eq1424 eq2022
    | exact resolve eq2022 eq1424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2022
  have eq2153 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (τ (M.op X4 X4)) X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq2111 X0 x x X3 X4
       have i₂ := eq1309 X0 X3 (M.op x x)
       grind)
    | (have i₁ := eq2111 x x x X3 X4
       have i₂ := eq1309 x (M.op (M.op (M.op x x) (M.op x x)) X3) X4
       grind)
    | exact superpose eq1309 eq2111
    | exact resolve eq2111 eq1309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1309 eq2111
  have eq2625 : ∀ X0 X1 X2 : G, (σ (M.op X1 X1)) ≠ (σ (M.op X0 (M.op X0 (M.op X1 X1)))) ∨ (M.op X2 X2) = (k X2 (σ (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq320 (M.op X1 X1) X2
       have i₂ := eq721 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq721 eq320
    | (have j0 := eq320 (M.op X1 X1) X2
       grind)
    | exact resolve eq320 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq2637 : ∀ X1 X2 : G, (σ (M.op X1 X1)) ≠ (σ (M.op X1 X1)) ∨ (M.op X2 X2) = (k X2 (σ (M.op X1 X1))) := by
    intro X1 X2
    first
    | (have i₁ := eq2625 x X1 X2
       have i₂ := eq1200 x X1 X1
       grind)
    | (have i₁ := eq2625 X1 X1 X2
       have i₂ := eq1200 x X1 (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq1200 eq2625
    | (have j0 := eq2625 x X1 X2
       grind)
    | exact resolve eq2625 eq1200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200 eq2625
  have eq2638 : ∀ X1 X2 : G, (M.op X2 X2) = (k X2 (σ (M.op X1 X1))) := by
    intro X1 X2
    first
    | (have j0 := eq2637 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2637
  have eq2703 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2638 (τ X0) X1
       have i₂ := eq196 X0
       grind)
    | exact superpose eq196 eq2638
    | exact resolve eq2638 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2763 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 (M.op X1 X1)
       have i₂ := eq2638 X1 X0
       grind)
    | exact superpose eq2638 eq20
    | exact resolve eq20 eq2638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2815 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2703 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq2703
    | exact resolve eq2703 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2703
  have eq3332 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X1)) = (k X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2815 X2 X0
       have i₂ := eq2815 X1 X0
       grind)
    | exact superpose eq2815 eq2815
    | exact resolve eq2815 eq2815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3419 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq198 X0
       have i₂ := eq2815 X1 (σ X0)
       grind)
    | exact superpose eq2815 eq198
    | exact resolve eq198 eq2815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq4394 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq310
       have i₂ := eq12 y x
       grind)
    | exact superpose eq12 eq310
    | (have j1 := eq12 x x
       grind)
    | exact resolve eq310 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq4398 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq4394
  have eq10860 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = (k (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1212 (τ X0) x
       have i₂ := eq196 X0
       grind)
    | exact superpose eq196 eq1212
    | exact resolve eq1212 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq56746 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq4398
       grind)
    | exact superpose eq4398 eq9
    | exact resolve eq9 eq4398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4398
  have eq56793 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq56746
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq56746
    | exact resolve eq56746 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56746
  have eq56794 : x = (M.op x x) := by grind
  clear eq56793
  have eq58658 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq721 X0 X1 x
       have i₂ := eq56794
       grind)
    | exact superpose eq56794 eq721
    | exact resolve eq721 eq56794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq58664 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq2638 x X0
       have i₂ := eq56794
       grind)
    | exact superpose eq56794 eq2638
    | exact resolve eq2638 eq56794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2638
  have eq58666 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) x) := by
    intro X0
    first
    | (have i₁ := eq2763 X0 x
       have i₂ := eq56794
       grind)
    | exact superpose eq56794 eq2763
    | exact resolve eq2763 eq56794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2763
  have eq58669 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq2815 x X0
       have i₂ := eq56794
       grind)
    | exact superpose eq56794 eq2815
    | exact resolve eq2815 eq56794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2815
  have eq58671 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = (k X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq3332 X0 X1 x
       have i₂ := eq56794
       grind)
    | exact superpose eq56794 eq3332
    | exact resolve eq3332 eq56794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3332 eq56794
  have eq62003 : ∀ X0 X1 : G, (M.op X1 (k X0 x)) = (k (k X0 x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1212 X0 x
       have i₂ := eq58669 X0
       grind)
    | exact superpose eq58669 eq1212
    | exact resolve eq1212 eq58669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62023 : ∀ X0 X1 : G, (k (σ X0) (M.op X1 X1)) = (σ (k X0 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq3419 X0 X1
       have i₂ := eq58669 X0
       grind)
    | exact superpose eq58669 eq3419
    | exact resolve eq3419 eq58669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3419
  have eq62082 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op X0 (k X0 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq1130 X1 X0 X0
       have i₂ := eq58669 X0
       grind)
    | exact superpose eq58669 eq1130
    | exact resolve eq1130 eq58669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130
  have eq62086 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (k X0 x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1440 X1 X0 X0
       have i₂ := eq58669 X0
       grind)
    | exact superpose eq58669 eq1440
    | exact resolve eq1440 eq58669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440
  have eq62274 : ∀ X0 X1 : G, (M.op (k X0 x) X1) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq62086 X0 X1
       have i₂ := eq58658 X0 X1
       grind)
    | exact superpose eq58658 eq62086
    | exact resolve eq62086 eq58658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62086
  have eq62277 : ∀ X0 : G, (M.op x X0) = (M.op X0 (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq62082 X0 x
       have i₂ := eq58658 x X0
       grind)
    | exact superpose eq58658 eq62082
    | exact resolve eq62082 eq58658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58658 eq62082
  have eq62307 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) x) := by
    intro X0
    first
    | (have i₁ := eq62023 X0 x
       have i₂ := eq58671 (σ X0) x
       grind)
    | exact superpose eq58671 eq62023
    | exact resolve eq62023 eq58671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58671 eq62023
  have eq74144 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = (M.op (k (τ (M.op X0 X0)) (σ x)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq519 X0 (τ (M.op X0 X0)) X1
       have i₂ := eq58664 (τ (M.op X0 X0))
       grind)
    | exact superpose eq58664 eq519
    | exact resolve eq519 eq58664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq74190 : ∀ X0 X1 : G, (k (M.op (σ X0) (σ X0)) (σ X1)) = (σ (k (k X0 (τ (σ x))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 X0 (σ x) X1
       have i₂ := eq58664 (σ X0)
       grind)
    | exact superpose eq58664 eq27
    | exact resolve eq27 eq58664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq58664
  have eq74201 : ∀ X0 X1 : G, (k (M.op (σ X0) (σ X0)) (σ X1)) = (σ (k (k X0 x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq74190 X0 X1
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq74190
    | exact resolve eq74190 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74190
  have eq74223 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = (M.op (M.op (σ x) (τ (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq74144 X0 X1
       have i₂ := eq10860 X0 (σ x)
       grind)
    | exact superpose eq10860 eq74144
    | exact resolve eq74144 eq10860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10860 eq74144
  have eq74456 : ∀ X0 X1 : G, (k (M.op (σ X0) (σ X0)) (σ X1)) = (σ (M.op X1 (k X0 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq74201 X0 X1
       have i₂ := eq62003 X0 X1
       grind)
    | exact superpose eq62003 eq74201
    | exact resolve eq74201 eq62003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62003 eq74201
  have eq74472 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = (M.op (τ (M.op X0 X0)) (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq74223 X0 X1
       have i₂ := eq1424 (τ (M.op X0 X0)) (σ x) X1
       grind)
    | exact superpose eq1424 eq74223
    | exact resolve eq74223 eq1424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1424 eq74223
  have eq74635 : ∀ X0 X1 : G, (M.op (σ X1) (M.op (σ X0) (σ X0))) = (σ (M.op X1 (k X0 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq74456 X0 X1
       have i₂ := eq1212 (σ X0) (σ X1)
       grind)
    | exact superpose eq1212 eq74456
    | exact resolve eq74456 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212 eq74456
  have eq74644 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = (M.op (σ x) (M.op (τ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq74472 X0 X1
       have i₂ := eq876 (σ x) X1 (τ (M.op X0 X0))
       grind)
    | (have i₁ := eq74472 X0 X1
       have i₂ := eq876 (τ (M.op X0 X0)) X1 (σ x)
       grind)
    | exact superpose eq876 eq74472
    | exact resolve eq74472 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876 eq74472
  have eq74741 : ∀ X0 X1 : G, (σ (M.op X1 (k X0 x))) = (M.op (σ X1) (k (σ X0) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq74635 X0 X1
       have i₂ := eq58669 (σ X0)
       grind)
    | exact superpose eq58669 eq74635
    | exact resolve eq74635 eq58669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58669 eq74635
  have eq74748 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq74644 X0 X1
       have i₂ := eq2153 (σ x) X1 X0
       grind)
    | (have i₁ := eq74644 X0 X1
       have i₂ := eq2153 (σ x) (M.op (τ (M.op X0 X0)) X1) x
       grind)
    | exact superpose eq2153 eq74644
    | exact resolve eq74644 eq2153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2153 eq74644
  have eq74820 : ∀ X0 X1 : G, (σ (M.op X1 (k X0 x))) = (M.op (σ X1) (σ (k X0 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq74741 X0 X1
       have i₂ := eq62307 X0
       grind)
    | exact superpose eq62307 eq74741
    | exact resolve eq74741 eq62307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74741
  have eq74823 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (k (τ X0) x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq74748 X0 X1
       have i₂ := eq58666 X0
       grind)
    | exact superpose eq58666 eq74748
    | exact resolve eq74748 eq58666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58666 eq74748
  have eq74878 : ∀ X1 : G, (M.op x X1) = (M.op (σ x) X1) := by
    intro X1
    first
    | (have i₁ := eq74823 x X1
       have i₂ := eq62274 (τ x) X1
       grind)
    | exact superpose eq62274 eq74823
    | exact resolve eq74823 eq62274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62274 eq74823
  have eq83652 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq74878 (σ y)
       grind)
    | exact superpose eq74878 eq14
    | exact resolve eq14 eq74878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74878
  have eq242241 : ∀ X0 : G, (M.op x (σ X0)) = (M.op (σ X0) (σ (k X0 x))) := by
    intro X0
    first
    | (have i₁ := eq62277 (σ X0)
       have i₂ := eq62307 X0
       grind)
    | exact superpose eq62307 eq62277
    | exact resolve eq62277 eq62307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62307
  have eq242310 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op X0 (k X0 x))) := by
    intro X0
    first
    | (have i₁ := eq242241 X0
       have i₂ := eq74820 X0 X0
       grind)
    | exact superpose eq74820 eq242241
    | exact resolve eq242241 eq74820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74820 eq242241
  have eq242370 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq242310 X0
       have i₂ := eq62277 X0
       grind)
    | exact superpose eq62277 eq242310
    | exact resolve eq242310 eq62277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62277 eq242310
  have eq278278 : (M.op x (σ y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq83652
       have i₂ := eq242370 y
       grind)
    | exact superpose eq242370 eq83652
    | (have r₁ := eq83652
       have r₂ := eq242370 y
       grind)
    | exact resolve eq83652 eq242370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83652 eq242370
  have eq278313 : False := by grind
  exact eq278313

/-- `Equation3591`: `x ◇ y = z ◇ ((x ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pyy_pyx_Equation3591 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3591 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3591.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X2) X1)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X0 X2) X1) (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op (M.op X0 X2) X1)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 (M.op X2 X3)) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op (M.op X0 (M.op X2 X3)) X1) X3
       have i₂ := eq8 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq41 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 X0 (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq41 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq67 : ∀ X0 X1 X2 : G, (τ X0) = (k X1 (τ X0)) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq47 X0 (σ X1) X2
       grind)
    | exact superpose eq47 eq28
    | (have j1 := eq47 (τ X0) X1 X2
       grind)
    | exact resolve eq28 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 (σ X0)) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq47 X0 (τ X1) X2
       grind)
    | exact superpose eq47 eq15
    | (have j1 := eq47 (σ X0) X1 X2
       grind)
    | exact resolve eq15 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq47 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq47 eq13
    | (have j1 := eq47 (σ X0) X2 X2
       grind)
    | exact resolve eq13 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq47 X0 X2 (τ X1)
       grind)
    | exact superpose eq47 eq15
    | (have j1 := eq47 X0 X2 X2
       grind)
    | exact resolve eq15 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq84 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op (M.op X0 X2) X1)) ∨ (k X3 X0) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X0 X2 X0 X1
       have i₂ := eq12 X3 X0
       grind)
    | exact superpose eq12 eq21
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op (M.op (M.op (M.op (M.op X4 X0) X5) X2) (M.op (M.op X4 X5) X1)) (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq21 (M.op (M.op X4 X0) X5) (M.op (M.op X4 X5) X1) X2 X3
       have i₂ := eq21 X4 X5 X0 X1
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 (M.op X3 X4)) X1)) = (M.op (M.op (M.op X3 X2) X4) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq21 X3 X4 X2 (M.op (M.op X0 (M.op X3 X4)) X1)
       have i₂ := eq8 X0 X1 (M.op X3 X4)
       grind)
    | exact superpose eq8 eq21
    | exact resolve eq21 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op (M.op X2 X3) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X2 X0) (M.op (M.op X2 X3) X1) X3
       have i₂ := eq21 X2 X3 X0 X1
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X0) X3) X4) = (M.op (M.op (M.op X2 X3) X1) (M.op (M.op X0 X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op (M.op X2 X0) X3) X4 (M.op (M.op X2 X3) X1)
       have i₂ := eq21 X2 X3 X0 X1
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op (M.op X0 X1) (M.op (M.op (M.op X4 X0) X5) (M.op (M.op X4 X5) X1))) X3)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq91 X0 X1 X2 X3 X4 X5
       have i₂ := eq93 (M.op X0 X1) X3 X2 (M.op (M.op X4 X0) X5) (M.op (M.op X4 X5) X1)
       grind)
    | exact superpose eq93 eq91
    | exact resolve eq91 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq109 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op X2 X1)) ∨ (k X3 X0) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq84 X0 X1 X2 X3
       have i₂ := eq96 X2 X1 X0 X2
       grind)
    | exact superpose eq96 eq84
    | (have j0 := eq84 X0 X1 X2 X3
       grind)
    | exact resolve eq84 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq110 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq102 X0 X1 X2 X3 x x
       have i₂ := eq21 x x X0 X1
       grind)
    | exact superpose eq21 eq102
    | exact resolve eq102 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq129 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 (M.op X3 X0)) X2) (M.op X4 X5)) = (M.op X3 (M.op (M.op X4 (M.op X0 (M.op X1 X2))) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq22 X4 X5 X3 (M.op (M.op X1 (M.op X3 X0)) X2)
       have i₂ := eq22 X1 X2 X3 X0
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op (M.op X2 X0) X3) X4)) = (M.op (M.op X2 X3) (M.op (M.op X0 X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq22 (M.op (M.op X2 X0) X3) X4 (M.op X2 X3) X1
       have i₂ := eq21 X2 X3 X0 X1
       grind)
    | exact superpose eq21 eq22
    | exact resolve eq22 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 (M.op X3 X0)) X2) X4) = (M.op (M.op (M.op X0 (M.op X1 X2)) X5) (M.op (M.op X3 X5) X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq21 X3 X5 (M.op (M.op X1 (M.op X3 X0)) X2) X4
       have i₂ := eq22 X1 X2 X3 X0
       grind)
    | exact superpose eq22 eq21
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X1 (M.op (M.op X4 X5) X0)) X2)) = (M.op (M.op (M.op X4 X3) X5) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq21 X4 X5 X3 (M.op (M.op X1 (M.op (M.op X4 X5) X0)) X2)
       have i₂ := eq22 X1 X2 (M.op X4 X5) X0
       grind)
    | exact superpose eq22 eq21
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X1 (M.op (M.op X4 X5) X0)) X2)) = (M.op X3 (M.op (M.op X0 (M.op X4 X5)) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq144 X0 X1 X2 X3 X4 X5
       have i₂ := eq93 X0 (M.op X1 X2) X3 X4 X5
       grind)
    | exact superpose eq93 eq144
    | exact resolve eq144 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq150 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 (M.op X3 X0)) X2) X4) = (M.op (M.op (M.op X0 X3) (M.op X1 X2)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq141 X0 X1 X2 X3 X4 x
       have i₂ := eq98 X3 x X0 (M.op X1 X2) X4
       grind)
    | exact superpose eq98 eq141
    | exact resolve eq141 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq141
  have eq157 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X4 (M.op X0 (M.op X1 X2))) X5)) = (M.op (M.op X3 X0) (M.op (M.op X4 (M.op X1 X2)) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq129 X0 X1 X2 X3 X4 X5
       have i₂ := eq93 X4 X5 (M.op X3 X0) X1 X2
       grind)
    | exact superpose eq93 eq129
    | exact resolve eq129 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq173 : ∀ X0 X1 X2 : G, (σ X0) = (σ (k X1 X0)) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq68 X0 (σ X1) X2
       grind)
    | exact superpose eq68 eq13
    | (have j1 := eq68 X0 X1 X2
       grind)
    | exact resolve eq13 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq224 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (M.op (σ X0) X2) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 (σ X0) X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq67
    | (have j0 := eq67 (σ X0) X1 X2
       grind)
    | exact resolve eq67 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq289 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq43 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq957 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X2 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74 X1 (σ X0) X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq74
    | (have j0 := eq74 X1 X1 X2
       grind)
    | exact resolve eq74 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1036 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X2 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq957 X0 X1 X2
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq957
    | (have j0 := eq957 X0 X1 X2
       grind)
    | exact resolve eq957 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq1282 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1036 X2 X0 (τ X1)
       grind)
    | exact superpose eq1036 eq15
    | (have j1 := eq1036 X2 X0 X2
       grind)
    | exact resolve eq15 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq1036
  have eq1323 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X2) X1) (M.op X3 X4)) = (M.op (M.op X2 X3) (M.op (M.op X0 X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq96 X3 X4 X2 (M.op (M.op X0 X2) X1)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq96
    | exact resolve eq96 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1357 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X2 (M.op X0 X1)
       have i₂ := eq96 X1 X2 X0 (M.op X0 X1)
       grind)
    | exact superpose eq96 eq8
    | exact resolve eq8 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1358 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X1) X4)) = (M.op (M.op X3 X0) (M.op (M.op X0 (M.op X1 X2)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq22 (M.op X3 X1) X4 (M.op X3 X0) X2
       have i₂ := eq96 X1 X2 X3 X0
       grind)
    | exact superpose eq96 eq22
    | exact resolve eq22 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1360 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op (M.op (M.op X3 X0) X2) (M.op (M.op X0 (M.op X1 X2)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op X3 X1) X4 (M.op (M.op X3 X0) X2)
       have i₂ := eq96 X1 X2 X3 X0
       grind)
    | exact superpose eq96 eq8
    | exact resolve eq8 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1363 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 X0) X2) (M.op X4 X5)) = (M.op (M.op X3 X1) (M.op (M.op X4 (M.op X0 (M.op X1 X2))) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq22 X4 X5 (M.op X3 X1) (M.op (M.op X3 X0) X2)
       have i₂ := eq96 X1 X2 X3 X0
       grind)
    | exact superpose eq96 eq22
    | exact resolve eq22 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq1372 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 X0) X2) (M.op X4 X5)) = (M.op X3 (M.op (M.op X4 (M.op X1 (M.op X0 (M.op X1 X2)))) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1363 X0 X1 X2 X3 X4 X5
       have i₂ := eq157 X1 X0 (M.op X1 X2) X3 X4 X5
       grind)
    | exact superpose eq157 eq1363
    | exact resolve eq1363 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1363
  have eq1375 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op X0 (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X2)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1360 X0 X1 X2 X3 X4
       have i₂ := eq93 (M.op X0 (M.op X1 X2)) X4 X0 X3 X2
       grind)
    | exact superpose eq93 eq1360
    | exact resolve eq1360 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1360
  have eq1377 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X1) X4)) = (M.op X3 (M.op (M.op X0 (M.op X0 (M.op X1 X2))) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1358 X0 X1 X2 X3 X4
       have i₂ := eq157 X0 X1 X2 X3 X0 X4
       grind)
    | exact superpose eq157 eq1358
    | exact resolve eq1358 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq1358
  have eq1392 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 (M.op X0 X1)) X4)) = (M.op (M.op X2 X3) (M.op (M.op X0 X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1323 X0 X1 X2 X3 X4
       have i₂ := eq93 X3 X4 X2 X0 X1
       grind)
    | exact superpose eq93 eq1323
    | exact resolve eq1323 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323
  have eq1397 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X4 (M.op X1 (M.op X0 (M.op X1 X2)))) X5)) = (M.op X0 (M.op (M.op X4 (M.op X3 X2)) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1372 X0 X1 X2 X3 X4 X5
       have i₂ := eq93 X4 X5 X0 X3 X2
       grind)
    | exact superpose eq93 eq1372
    | exact resolve eq1372 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq1372
  have eq1400 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op X0 (M.op (M.op (M.op X2 X1) (M.op X0 (M.op X3 X2))) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1375 X0 X1 X2 X3 X4
       have i₂ := eq150 X2 X0 (M.op X3 X2) X1 X4
       grind)
    | (have i₁ := eq1375 X0 X1 X2 X1 X4
       have i₂ := eq150 X0 X1 X2 (M.op X1 X2) X4
       grind)
    | exact superpose eq150 eq1375
    | exact resolve eq1375 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375
  have eq1410 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op (M.op X3 X2) (M.op (M.op X2 X1) X4)) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq1400 x X1 X2 X3 X4
       have i₂ := eq22 (M.op X2 X1) X4 x (M.op X3 X2)
       grind)
    | exact superpose eq22 eq1400
    | exact resolve eq1400 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400
  have eq1415 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op X3 (M.op (M.op X2 (M.op X2 X1)) X4)) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq1410 X1 X2 X3 X4
       have i₂ := eq1392 X2 X1 X3 X2 X4
       grind)
    | (have i₁ := eq1410 (M.op x X1) X3 X3 X4
       have i₂ := eq1392 x X1 (M.op X3 X3) X3 X4
       grind)
    | exact superpose eq1392 eq1410
    | exact resolve eq1410 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410
  have eq1423 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op (M.op X1 (M.op X3 X0)) X2) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1357 X3 (M.op (M.op X1 (M.op X3 X0)) X2) X4
       have i₂ := eq22 X1 X2 X3 X0
       grind)
    | exact superpose eq22 eq1357
    | exact resolve eq1357 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1435 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X3) X1)) = (M.op (M.op X2 X3) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1357 X2 X3 (M.op (M.op X0 X3) X1)
       have i₂ := eq8 X0 X1 X3
       grind)
    | exact superpose eq8 eq1357
    | exact resolve eq1357 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1452 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op (M.op X0 X2) X3) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X0 X3 X2 (M.op X3 X1)
       have i₂ := eq1357 X0 X3 X1
       grind)
    | exact superpose eq1357 eq21
    | exact resolve eq21 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1454 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X0 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X0 X1) X0
       have i₂ := eq1357 X2 X0 X1
       grind)
    | exact superpose eq1357 eq8
    | exact resolve eq8 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1457 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) X3)) = (M.op X2 (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 (M.op X0 X1) X3 X1 X2
       have i₂ := eq1357 X0 X1 X2
       grind)
    | exact superpose eq1357 eq22
    | exact resolve eq22 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1458 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op x x)
       have i₂ := eq1357 x x x
       grind)
    | exact superpose eq1357 eq11
    | (have r₁ := eq11 X0 (M.op x x)
       have r₂ := eq1357 x x x
       grind)
    | exact resolve eq11 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1461 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X1) X3) = (M.op (M.op (M.op X0 X1) X4) (M.op (M.op (M.op X0 X2) X4) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq21 (M.op X0 X2) X4 (M.op X2 X1) X3
       have i₂ := eq1357 X0 X2 X1
       grind)
    | exact superpose eq1357 eq21
    | exact resolve eq21 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1470 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1458 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1458
  have eq1475 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X1) X3) = (M.op (M.op X0 X4) (M.op (M.op X2 (M.op (M.op X0 X1) X4)) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1461 X0 X1 X2 X3 X4
       have i₂ := eq135 X2 (M.op (M.op X0 X1) X4) X0 X4 X3
       grind)
    | (have i₁ := eq1461 X0 X1 X2 X4 X1
       have i₂ := eq135 (M.op X0 X2) X1 (M.op X0 X1) X1 X4
       grind)
    | exact superpose eq135 eq1461
    | exact resolve eq1461 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq1461
  have eq1479 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X0 (M.op (M.op (M.op X0 X2) X3) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1452 X0 X1 X2 X3
       have i₂ := eq1454 X0 X1 (M.op (M.op X0 X2) X3)
       grind)
    | (have i₁ := eq1452 X0 X1 X2 X3
       have i₂ := eq1454 (M.op (M.op X0 X2) X3) X1 X0
       grind)
    | exact superpose eq1454 eq1452
    | exact resolve eq1452 eq1454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452 eq1454
  have eq1492 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op X2 (M.op (M.op (M.op X1 (M.op X3 X0)) (M.op X0 (M.op X1 X2))) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1423 X0 X1 X2 X3 X4
       have i₂ := eq1457 (M.op X1 (M.op X3 X0)) (M.op X0 (M.op X1 X2)) X2 X4
       grind)
    | (have i₁ := eq1423 X0 X1 X2 X3 X4
       have i₂ := eq1457 (M.op X1 (M.op X3 X0)) X2 (M.op X0 (M.op X1 X2)) X4
       grind)
    | exact superpose eq1457 eq1423
    | exact resolve eq1423 eq1457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1423
  have eq1498 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X1) X3) = (M.op (M.op X0 X4) (M.op (M.op X4 (M.op X0 X1)) (M.op X2 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1475 X0 X1 X2 X3 X4
       have i₂ := eq148 X4 X2 X3 (M.op X0 X4) X0 X1
       grind)
    | (have i₁ := eq1475 X0 X1 X0 (M.op X1 X2) x
       have i₂ := eq148 X0 X1 X2 (M.op X0 x) (M.op X0 X1) x
       grind)
    | exact superpose eq148 eq1475
    | exact resolve eq1475 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475
  have eq1508 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op X2 (M.op (M.op (M.op X0 X3) (M.op X1 (M.op X0 (M.op X1 X2)))) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1492 X0 X1 X2 X3 X4
       have i₂ := eq150 X0 X1 (M.op X0 (M.op X1 X2)) X3 X4
       grind)
    | (have i₁ := eq1492 X1 X0 X2 X3 X4
       have i₂ := eq150 X0 X1 (M.op X0 X2) (M.op X3 X1) X4
       grind)
    | exact superpose eq150 eq1492
    | exact resolve eq1492 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq1492
  have eq1512 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X1) X3) = (M.op X0 (M.op (M.op X4 (M.op X4 (M.op X0 X1))) (M.op X2 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1498 X0 X1 X2 X3 X4
       have i₂ := eq1392 X4 (M.op X0 X1) X0 X4 (M.op X2 X3)
       grind)
    | (have i₁ := eq1498 X0 X1 X2 X3 X3
       have i₂ := eq1392 X0 X1 (M.op X0 X3) X3 (M.op X2 X3)
       grind)
    | exact superpose eq1392 eq1498
    | exact resolve eq1498 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392 eq1498
  have eq1516 : ∀ X0 X2 X3 X4 : G, (M.op X3 X4) = (M.op X0 (M.op (M.op (M.op X0 X3) (M.op X2 X2)) X4)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq1508 X0 x X2 X3 X4
       have i₂ := eq1397 X0 x X2 X2 (M.op X0 X3) X4
       grind)
    | exact superpose eq1397 eq1508
    | exact resolve eq1508 eq1397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397 eq1508
  have eq1518 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X3) = (M.op X1 (M.op (M.op X0 X0) (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1512 X0 X1 X2 X3 x
       have i₂ := eq1377 x X0 X1 X0 (M.op X2 X3)
       grind)
    | exact superpose eq1377 eq1512
    | exact resolve eq1512 eq1377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377 eq1512
  have eq1521 : ∀ X2 X3 X4 : G, (M.op X3 X4) = (M.op X3 (M.op (M.op X2 X2) X4)) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq1516 x X2 X3 X4
       have i₂ := eq1479 x X4 X3 (M.op X2 X2)
       grind)
    | exact superpose eq1479 eq1516
    | exact resolve eq1516 eq1479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479 eq1516
  have eq1523 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X3) = (M.op X1 (M.op X0 (M.op (M.op X2 X0) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1518 X0 X1 X2 X3
       have i₂ := eq1435 X2 X3 X0 X0
       grind)
    | (have i₁ := eq1518 X0 X1 (M.op X0 X3) X1
       have i₂ := eq1435 X0 X1 (M.op X0 X0) X3
       grind)
    | exact superpose eq1435 eq1518
    | exact resolve eq1518 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435 eq1518
  have eq1525 : ∀ X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op (M.op X2 X1) X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq1523 x X1 X2 X3
       have i₂ := eq8 X2 X3 x
       grind)
    | exact superpose eq8 eq1523
    | exact resolve eq1523 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1523
  have eq1572 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X3 X4) (M.op X3 X4)) X1) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X0 X2 (M.op (M.op (M.op X3 X4) (M.op X3 X4)) X1)
       have i₂ := eq110 X3 X4 X0 X1
       grind)
    | exact superpose eq110 eq8
    | exact resolve eq8 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq1612 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X2) = (M.op X1 (M.op (M.op X0 (M.op (M.op (M.op X3 X4) (M.op X3 X4)) X1)) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1572 X0 X1 X2 X3 X4
       have i₂ := eq1457 X0 (M.op (M.op (M.op X3 X4) (M.op X3 X4)) X1) X1 X2
       grind)
    | (have i₁ := eq1572 X0 X1 X2 X3 X4
       have i₂ := eq1457 X0 X1 (M.op (M.op (M.op X3 X4) (M.op X3 X4)) X1) X2
       grind)
    | exact superpose eq1457 eq1572
    | exact resolve eq1572 eq1457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1572
  have eq1650 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X2) = (M.op X1 (M.op (M.op X1 (M.op (M.op X3 X4) (M.op X3 X4))) (M.op X0 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1612 X0 X1 X2 X3 X4
       have i₂ := eq148 X1 X0 X2 X1 (M.op X3 X4) (M.op X3 X4)
       grind)
    | (have i₁ := eq1612 X0 x (M.op X1 X2) X3 X4
       have i₂ := eq148 X0 X1 X2 x (M.op (M.op X3 X4) (M.op X3 X4)) x
       grind)
    | exact superpose eq148 eq1612
    | exact resolve eq1612 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1612
  have eq1681 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X2) = (M.op X1 (M.op (M.op (M.op X3 X4) (M.op X3 X4)) (M.op X1 (M.op X0 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1650 X0 X1 X2 X3 X4
       have i₂ := eq148 (M.op X3 X4) X1 (M.op X0 X2) X1 X3 X4
       grind)
    | (have i₁ := eq1650 X1 X0 X2 X3 X4
       have i₂ := eq148 X0 X1 X2 X0 (M.op X3 X4) (M.op X3 X4)
       grind)
    | exact superpose eq148 eq1650
    | exact resolve eq1650 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq1650
  have eq1707 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1681 X0 X1 X2 x x
       have i₂ := eq1521 (M.op x x) X1 (M.op X1 (M.op X0 X2))
       grind)
    | (have i₁ := eq1681 X0 x X2 x x
       have i₂ := eq1521 X2 x (M.op (M.op (M.op x x) (M.op x x)) (M.op x (M.op X0 X2)))
       grind)
    | exact superpose eq1521 eq1681
    | exact resolve eq1681 eq1521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1521 eq1681
  have eq1869 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq289 (M.op X0 X0)
       have i₂ := eq1470 X0 (M.op X0 X0)
       grind)
    | exact superpose eq1470 eq289
    | (have j0 := eq289 (M.op X0 X0)
       grind)
    | exact resolve eq289 eq1470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470
  have eq1879 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq289 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq289
    | (have j0 := eq289 (τ X0)
       grind)
    | exact resolve eq289 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq289
  have eq1887 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1869 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869
  have eq1893 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1879 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1879
    | (have j0 := eq1879 X0
       grind)
    | exact resolve eq1879 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879
  have eq1901 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1893 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1893
    | (have j0 := eq1893 X0
       grind)
    | exact resolve eq1893 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1893
  have eq2070 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1707 X1 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq1707
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq1707 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2245 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ X1 ∨ (M.op X0 (M.op X0 X1)) = (k X2 X1) ∨ (M.op X1 X3) = (k X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq109 X1 X1 X2 X3
       grind)
    | exact superpose eq109 eq11
    | (have j1 := eq109 X1 X1 X2 X3
       grind)
    | exact resolve eq11 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq2387 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (k X2 X1) ∨ (M.op X1 X3) = (k X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq2245 X0 X1 X2 X3
       have j1 := eq2070 X1 X1 X3
       grind)
    | (have r₁ := eq2245 X1 X0 X2 X3
       have r₂ := eq2070 X0 X1 X2
       grind)
    | exact resolve eq2245 eq2070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070 eq2245
  have eq4508 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq72 x y X0
       grind)
    | exact superpose eq72 eq14
    | (have j1 := eq72 x x X0
       grind)
    | exact resolve eq14 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq4588 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq4508 X0
       have j1 := eq1282 x X0 x
       grind)
    | (have r₁ := eq4508 X0
       have r₂ := eq1282 x x y
       grind)
    | exact resolve eq4508 eq1282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282 eq4508
  have eq4631 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1901 (σ x)
       have i₂ := eq4588 (σ x)
       grind)
    | exact superpose eq4588 eq1901
    | (have j0 := eq1901 (σ x)
       grind)
    | (have r₁ := eq1901 (σ x)
       have r₂ := eq4588 (σ x)
       grind)
    | exact resolve eq1901 eq4588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4648 : ∀ X0 : G, (τ (σ x)) = (k X0 (τ (σ x))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (σ x)
       have i₂ := eq4588 (σ X0)
       grind)
    | exact superpose eq4588 eq28
    | exact resolve eq28 eq4588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4588
  have eq4653 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4631
  have eq4654 : ∀ X0 : G, x = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq4648 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq4648
    | exact resolve eq4648 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4648
  have eq4805 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1901 x
       have i₂ := eq4654 x
       grind)
    | exact superpose eq4654 eq1901
    | (have j0 := eq1901 x
       grind)
    | (have r₁ := eq1901 x
       have r₂ := eq4654 x
       grind)
    | exact resolve eq1901 eq4654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1901 eq4654
  have eq4824 : x = (M.op x x) := by grind
  clear eq4805
  have eq4844 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op x X1) (M.op (M.op x X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 x X1 x X0
       have i₂ := eq4824
       grind)
    | exact superpose eq4824 eq21
    | exact resolve eq21 eq4824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq4859 : ∀ X0 : G, x = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq1707 x x x
       have i₂ := eq4824
       grind)
    | exact superpose eq4824 eq1707
    | exact resolve eq1707 eq4824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4869 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op (M.op x (M.op x X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4844 X0 X1
       have i₂ := eq1457 x (M.op x X1) X1 X0
       grind)
    | (have i₁ := eq4844 X0 X1
       have i₂ := eq1457 x X1 (M.op x X1) X0
       grind)
    | exact superpose eq1457 eq4844
    | exact resolve eq4844 eq1457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1457 eq4844
  have eq4874 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4869 X0 X1
       have i₂ := eq1415 X1 x X1 X0
       grind)
    | (have i₁ := eq4869 X0 (M.op x X1)
       have i₂ := eq1415 X1 x x (M.op (M.op x (M.op x (M.op x X1))) X0)
       grind)
    | exact superpose eq1415 eq4869
    | exact resolve eq4869 eq1415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1415 eq4869
  have eq4876 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4874 X0 X1
       have i₂ := eq1525 X1 X1 X0
       grind)
    | exact superpose eq1525 eq4874
    | exact resolve eq4874 eq1525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1525 eq4874
  have eq9519 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq1357 (σ x) (σ x) X0
       have i₂ := eq4653
       grind)
    | exact superpose eq4653 eq1357
    | exact resolve eq1357 eq4653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357
  have eq9524 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq1707 (σ x) x (σ x)
       have i₂ := eq4653
       grind)
    | exact superpose eq4653 eq1707
    | exact resolve eq1707 eq4653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1707 eq4653
  have eq9527 : (σ x) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq9524 x
       have i₂ := eq4876 (σ x) x
       grind)
    | exact superpose eq4876 eq9524
    | exact resolve eq9524 eq4876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9524
  have eq9530 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq9519 X0
       have i₂ := eq4876 X0 (σ x)
       grind)
    | exact superpose eq4876 eq9519
    | exact resolve eq9519 eq4876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9519
  have eq15951 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq9530 (σ y)
       grind)
    | exact superpose eq9530 eq14
    | exact resolve eq14 eq9530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9530
  have eq140067 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op x (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4876 (σ (M.op X0 X0)) (σ (M.op X0 X0))
       have i₂ := eq1887 X0
       grind)
    | exact superpose eq1887 eq4876
    | exact resolve eq4876 eq1887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140074 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op x (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq140067 X0
       have i₂ := eq1887 X0
       grind)
    | exact superpose eq1887 eq140067
    | exact resolve eq140067 eq1887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1887 eq140067
  have eq145925 : ∀ X0 X1 : G, (σ X0) = (M.op x (σ X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq140074 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq140074
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq140074 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140074
  have eq149127 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ (M.op X2 (M.op X2 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2387 X0 X1 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2387
  have eq149130 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op x X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq149127 X0 X1 x
       have i₂ := eq4876 X1 x
       grind)
    | exact superpose eq4876 eq149127
    | (have j0 := eq149127 X0 X1 x
       grind)
    | (have r₁ := eq149127 (M.op X1 (M.op x X1)) X1 x
       have r₂ := eq4876 (M.op x X1) X1
       grind)
    | (have r₁ := eq149127 x x X1
       have r₂ := eq4876 x X1
       grind)
    | exact resolve eq149127 eq4876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149127
  have eq156481 : ∀ X0 X1 : G, (M.op x X0) ≠ (M.op x X1) ∨ (k (M.op X1 X0) X1) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq149130 (M.op X1 X0) X1
       have i₂ := eq4876 X0 X1
       grind)
    | exact superpose eq4876 eq149130
    | (have r₁ := eq149130 (M.op X0 X0) X0
       have r₂ := eq4876 X0 X0
       grind)
    | exact resolve eq149130 eq4876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4876 eq149130
  have eq288319 : ∀ X0 : G, (M.op x X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq156481 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156481
  have eq288673 : ∀ X0 X1 : G, (σ X0) = (σ (M.op x X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq173 X0 (M.op X0 X0) X1
       have i₂ := eq288319 X0
       grind)
    | exact superpose eq288319 eq173
    | (have j0 := eq173 X0 X1 X1
       grind)
    | exact resolve eq173 eq288319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq289258 : ∀ X0 : G, (σ y) ≠ (M.op x (σ y)) ∨ (M.op y X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq15951
       have i₂ := eq288673 y X0
       grind)
    | exact superpose eq288673 eq15951
    | (have j1 := eq288673 y X0
       grind)
    | exact resolve eq15951 eq288673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288673
  have eq289320 : ∀ X0 : G, (M.op y X0) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq289258 X0
       have j1 := eq145925 y X0
       grind)
    | (have r₁ := eq289258 X0
       have r₂ := eq145925 y x
       grind)
    | exact resolve eq289258 eq145925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145925 eq289258
  have eq289546 : ∀ X0 X1 : G, y = (M.op y X0) ∨ (k X1 (σ y)) = (M.op (σ y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq224 y X0 X1
       have i₂ := eq289320 X0
       grind)
    | exact superpose eq289320 eq224
    | (have j0 := eq224 y X1 X1
       grind)
    | exact resolve eq224 eq289320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq310998 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq4859 y
       have i₂ := eq289546 (M.op y x) X0
       grind)
    | exact superpose eq289546 eq4859
    | (have j1 := eq289546 X0 X0
       grind)
    | exact resolve eq4859 eq289546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4859 eq289546
  have eq311089 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq310998 (σ X0)
       grind)
    | exact superpose eq310998 eq13
    | exact resolve eq13 eq310998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310998
  have eq311102 : ∀ X0 : G, (σ (M.op y X0)) = (M.op (σ y) (σ X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq311089 X0
       have i₂ := eq289320 X0
       grind)
    | exact superpose eq289320 eq311089
    | exact resolve eq311089 eq289320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289320 eq311089
  have eq311186 : (M.op x (σ y)) = (k (σ (M.op y y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq288319 (σ y)
       have i₂ := eq311102 y
       grind)
    | exact superpose eq311102 eq288319
    | exact resolve eq288319 eq311102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311102
  have eq311215 : (M.op x (σ y)) = (σ (k (M.op y y) y)) ∨ x = y := by
    first
    | (have i₁ := eq311186
       have i₂ := eq13 (M.op y y) y
       grind)
    | exact superpose eq13 eq311186
    | exact resolve eq311186 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311186
  have eq311245 : (σ (M.op x y)) = (M.op x (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq311215
       have i₂ := eq288319 y
       grind)
    | exact superpose eq288319 eq311215
    | exact resolve eq311215 eq288319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288319 eq311215
  have eq311249 : x = y := by
    first
    | (have r₁ := eq311245
       have r₂ := eq15951
       grind)
    | exact resolve eq311245 eq15951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311245
  have eq316079 : (M.op x (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq15951
       have i₂ := eq311249
       grind)
    | exact superpose eq311249 eq15951
    | exact resolve eq15951 eq311249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15951 eq311249
  have eq316098 : (σ x) ≠ (M.op x (σ x)) := by
    first
    | (have i₁ := eq316079
       have i₂ := eq4824
       grind)
    | exact superpose eq4824 eq316079
    | exact resolve eq316079 eq4824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4824 eq316079
  have eq316104 : False := by grind
  exact eq316104

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation3600 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3600 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op (M.op X1 X0) X1) X3
       have i₂ := eq8 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq19 X0 X1 x X3
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq26 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq36 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X0 X2
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq41 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 X1 x
       have i₂ := eq21 X0 X1 x
       grind)
    | exact superpose eq21 eq36
    | (have j0 := eq36 X0 X1 x
       grind)
    | exact resolve eq36 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq64 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq69 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq235 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq69
  have eq250 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq235 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq235
    | exact resolve eq235 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq406 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X2 (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (σ X0) (σ X0) x
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq21
    | (have j1 := eq39 X1 X0
       grind)
    | exact resolve eq21 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq409 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq39 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq926 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq409 (M.op X0 X1)
       have i₂ := eq26 X0 X1
       grind)
    | exact superpose eq26 eq409
    | (have j0 := eq409 (M.op X0 X1)
       grind)
    | exact resolve eq409 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq409
  have eq932 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq926 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926
  have eq1065 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq1155 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1065 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1065
    | (have j0 := eq1065 X0 X1
       grind)
    | exact resolve eq1065 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065
  have eq1678 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (σ (M.op X0 X1)) (σ (M.op X0 X1)) x
       have i₂ := eq932 X0 X1
       grind)
    | exact superpose eq932 eq21
    | exact resolve eq21 eq932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932
  have eq2202 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X2 (σ X0)) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1678 X1 X1 X2
       have i₂ := eq1155 X0 X1
       grind)
    | (have i₁ := eq1678 X0 X1 X2
       have i₂ := eq1155 (M.op X0 X1) X1
       grind)
    | exact superpose eq1155 eq1678
    | (have j1 := eq1155 X0 X1
       grind)
    | exact resolve eq1678 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155 eq1678
  have eq2760 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq406 y x X0
       grind)
    | exact superpose eq406 eq14
    | (have j1 := eq406 y x X0
       grind)
    | exact resolve eq14 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq2797 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq2760 X0
       have j1 := eq2202 y x X0
       grind)
    | (have r₁ := eq2760 X0
       have r₂ := eq2202 y x x
       grind)
    | exact resolve eq2760 eq2202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2202 eq2760
  have eq2858 : y = (k y (τ (σ y))) := by
    first
    | (have i₁ := eq250 y
       have i₂ := eq2797 (σ y)
       grind)
    | exact superpose eq2797 eq250
    | exact resolve eq250 eq2797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq2860 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2797 (σ x)
       grind)
    | exact superpose eq2797 eq14
    | exact resolve eq14 eq2797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2797
  have eq2864 : y = (k y y) := by
    first
    | (have i₁ := eq2858
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2858
    | exact resolve eq2858 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2858
  have eq2975 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq41 y y
       have i₂ := eq2864
       grind)
    | exact superpose eq2864 eq41
    | (have j0 := eq41 y y
       grind)
    | exact resolve eq41 eq2864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq2864
  have eq2978 : y = (M.op y y) := by grind
  clear eq2975
  have eq3174 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq21 y y x
       have i₂ := eq2978
       grind)
    | exact superpose eq2978 eq21
    | exact resolve eq21 eq2978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq2978
  have eq3704 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2860
       have i₂ := eq3174 x
       grind)
    | exact superpose eq3174 eq2860
    | exact resolve eq2860 eq3174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2860 eq3174
  have eq3708 : False := by grind
  exact eq3708
