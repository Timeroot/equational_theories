import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4411`: `x ◇ (x ◇ y) = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pyx_Equation4411 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4411 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4411.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X0) := by
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
  have eq17 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X3) X2) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X2 X0) X3
       have i₂ := eq8 X2 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X0 X3
       have i₂ := eq8 X2 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X2 (M.op X2 X0)
       have i₂ := eq8 X2 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X1 X3))) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X1 X3) X0
       have i₂ := eq8 X0 X1 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17 X0 X1 X2 X3
       have i₂ := eq20 X2 X0 X3 X2
       grind)
    | exact superpose eq20 eq17
    | exact resolve eq17 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq28 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
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
  have eq31 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq32 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 X0 X0
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq33 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq28 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq75 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26
    | exact resolve eq26 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X2 (σ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq33 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq33 eq13
    | (have j1 := eq33 (σ X0) X2 X2
       grind)
    | exact resolve eq13 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq33 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq120 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X3) (M.op (M.op X0 X1) X2)) = (M.op (M.op (M.op X4 X5) X2) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq20 X4 X5 X2 (M.op X0 X3)
       have i₂ := eq19 X0 X3 X2 X1
       grind)
    | (have i₁ := eq20 X4 X5 X2 (M.op X0 X3)
       have i₂ := eq19 X0 X1 X2 X3
       grind)
    | exact superpose eq19 eq20
    | exact resolve eq20 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20
  have eq188 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X4)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq22 x x X0 X4
       have i₂ := eq22 x x X0 X1
       grind)
    | (have i₁ := eq22 X0 X1 (M.op X0 X1) x
       have i₂ := eq22 X0 X1 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X4) X0) = (M.op X0 (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X0 X3 X4
       have i₂ := eq22 X1 X2 X0 X3
       grind)
    | (have i₁ := eq8 (M.op X0 X1) (M.op X0 X1) X2
       have i₂ := eq22 X0 X1 (M.op X0 X1) X3
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X2 X3
       have i₂ := eq188 X0 X2 X1
       grind)
    | (have i₁ := eq8 X0 X2 X3
       have i₂ := eq188 X0 X1 X2
       grind)
    | exact superpose eq188 eq8
    | exact resolve eq8 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq532 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X4) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X2 X3 X4
       have i₂ := eq402 X2 X3 X0 X1
       grind)
    | exact superpose eq402 eq8
    | exact resolve eq8 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X5 (M.op X5 X3)) X2) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq21 X5 X3 X2 x
       have i₂ := eq402 X2 (M.op X3 x) X0 X1
       grind)
    | exact superpose eq402 eq21
    | exact resolve eq21 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq1199 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq31 x y
       grind)
    | exact superpose eq31 eq14
    | (have j1 := eq31 x x
       grind)
    | exact resolve eq14 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1201 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq11
    | (have j0 := eq11 X1 (σ X0)
       have j1 := eq31 X0 X1
       grind)
    | (have r₁ := eq11 X0 (σ X0)
       have r₂ := eq31 X0 X1
       grind)
    | exact resolve eq11 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1214 : ∀ X0 X1 X2 X3 : G, (M.op (σ X1) (σ (k X0 X1))) = (M.op (σ X1) (M.op (M.op X2 X3) (σ X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 X2 X3 (σ X1) (σ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq22
    | (have j1 := eq31 X1 X1
       grind)
    | exact resolve eq22 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1250 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq1254 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1201 X0 X1
       have j1 := eq11 X1 (σ X0)
       grind)
    | (have r₁ := eq1201 X0 X1
       have r₂ := eq11 X0 (σ X0)
       grind)
    | exact resolve eq1201 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201
  have eq1921 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) ≠ (M.op (M.op X3 X4) X2) ∨ (M.op (M.op X3 X4) X2) = (k (M.op (M.op X3 X4) X2) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq98 (M.op (M.op X3 X4) X2) X2
       have i₂ := eq222 X2 X3 X4 X0 X1
       grind)
    | exact superpose eq222 eq98
    | (have j0 := eq98 (M.op (M.op X3 X4) X2) X2
       grind)
    | (have r₁ := eq98 (M.op (M.op X3 X4) X0) X0
       have r₂ := eq222 X0 X3 X4 X3 X4
       grind)
    | exact resolve eq98 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq1944 : ∀ X2 X3 X4 : G, (M.op (M.op X3 X4) X2) = (k (M.op (M.op X3 X4) X2) X2) := by
    intro X2 X3 X4
    first
    | (have j0 := eq1921 x x X2 X3 X4
       grind)
    | (have r₁ := eq1921 x x X2 X3 X4
       have r₂ := eq532 x x X2 X3 X4
       grind)
    | (have r₁ := eq1921 X3 X4 X2 x x
       have r₂ := eq532 x x X2 X3 X4
       grind)
    | exact resolve eq1921 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1921
  have eq2199 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1254 (τ X0) X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq1254
    | (have j0 := eq1254 (τ X0) X1
       grind)
    | exact resolve eq1254 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254
  have eq2202 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2199 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2199
    | (have j0 := eq2199 X0 X1
       grind)
    | exact resolve eq2199 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2199
  have eq2205 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2202 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2202
    | (have j0 := eq2202 X0 X1
       grind)
    | exact resolve eq2202 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2202
  have eq2216 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2205 (τ X0) X1
       have i₂ := eq75 X0 X0
       grind)
    | exact superpose eq75 eq2205
    | (have j0 := eq2205 (τ X0) X1
       grind)
    | exact resolve eq2205 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2205
  have eq2598 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq32
    | (have j0 := eq32 X1 X1
       grind)
    | exact resolve eq32 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq2696 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2598 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2598
    | (have j0 := eq2598 X0 X1
       grind)
    | exact resolve eq2598 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2598
  have eq7113 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1250 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq1250
    | (have j0 := eq1250 (τ X0)
       grind)
    | exact resolve eq1250 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7121 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7113 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7113
    | (have j0 := eq7113 X0
       grind)
    | exact resolve eq7113 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7113
  have eq7127 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7121 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7121
    | (have j0 := eq7121 X0
       grind)
    | exact resolve eq7121 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7121
  have eq12417 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1199
       have i₂ := eq2696 y x
       grind)
    | exact superpose eq2696 eq1199
    | (have j1 := eq2696 x (σ x)
       grind)
    | (have r₁ := eq1199
       have r₂ := eq2696 y x
       grind)
    | exact resolve eq1199 eq2696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199 eq2696
  have eq12419 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq12417
  have eq12427 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq11 X0 (σ x)
       have i₂ := eq12419
       grind)
    | exact superpose eq12419 eq11
    | (have j0 := eq11 X0 (σ x)
       grind)
    | (have r₁ := eq11 X0 (σ x)
       have r₂ := eq12419
       grind)
    | (have r₁ := eq11 X0 x
       have r₂ := eq12419
       grind)
    | exact resolve eq11 eq12419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12419
  have eq12486 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq12427 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12427
  have eq12679 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq2216 (σ x) X0
       have i₂ := eq12486 (σ x)
       grind)
    | exact superpose eq12486 eq2216
    | (have j0 := eq2216 (σ x) X0
       grind)
    | exact resolve eq2216 eq12486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2216 eq12486
  have eq12705 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq12679 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12679
  have eq12715 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12705 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq12705
    | exact resolve eq12705 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12705
  have eq12727 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq12715 X0
       have j1 := eq11 X0 x
       grind)
    | (have r₁ := eq12715 X0
       have r₂ := eq11 X0 x
       grind)
    | exact resolve eq12715 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12715
  have eq12930 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq7127 x
       have i₂ := eq12727 x
       grind)
    | exact superpose eq12727 eq7127
    | (have j0 := eq7127 x
       grind)
    | (have r₁ := eq7127 x
       have r₂ := eq12727 x
       grind)
    | exact resolve eq7127 eq12727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12931 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1250 x
       have i₂ := eq12727 x
       grind)
    | exact superpose eq12727 eq1250
    | (have j0 := eq1250 x
       grind)
    | exact resolve eq1250 eq12727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250 eq12727
  have eq12957 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq12931
  have eq12958 : x = (M.op x x) := by grind
  clear eq12930
  have eq13582 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (M.op x X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq222 X2 x x X0 X1
       have i₂ := eq12958
       grind)
    | exact superpose eq12958 eq222
    | exact resolve eq222 eq12958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq13588 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq402 X0 X1 x x
       have i₂ := eq12958
       grind)
    | exact superpose eq12958 eq402
    | exact resolve eq402 eq12958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq13591 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op x X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq532 X0 X1 X2 x x
       have i₂ := eq12958
       grind)
    | exact superpose eq12958 eq532
    | exact resolve eq532 eq12958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq13596 : ∀ X0 : G, (M.op x X0) = (k (M.op x X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1944 x x x
       have i₂ := eq12958
       grind)
    | exact superpose eq12958 eq1944
    | exact resolve eq1944 eq12958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1944
  have eq13602 : ∀ X2 : G, (M.op x X2) = (M.op X2 (M.op x X2)) := by
    intro X2
    first
    | (have i₁ := eq13582 x x X2
       have i₂ := eq13591 x x X2
       grind)
    | exact superpose eq13591 eq13582
    | exact resolve eq13582 eq13591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13582
  have eq19992 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X4)) = (M.op (M.op X6 (M.op X6 X7)) (M.op (M.op X3 X5) X2)) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq539 X3 X4 (M.op (M.op X3 X5) X2) X7 X6
       have i₂ := eq120 X3 X5 X2 X4 X0 X1
       grind)
    | exact superpose eq120 eq539
    | exact resolve eq539 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq20345 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X4)) = (M.op x (M.op (M.op X3 X5) X2)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq19992 X0 X1 X2 X3 X4 X5 x x
       have i₂ := eq13591 x (M.op x x) (M.op (M.op X3 X5) X2)
       grind)
    | exact superpose eq13591 eq19992
    | exact resolve eq19992 eq13591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19992
  have eq20475 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X4)) = (M.op x (M.op x X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20345 X0 X1 X2 X3 X4 x
       have i₂ := eq13591 X3 x X2
       grind)
    | exact superpose eq13591 eq20345
    | exact resolve eq20345 eq13591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20345
  have eq20604 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X4)) = (M.op x x) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20475 X0 X1 X2 X3 X4
       have i₂ := eq13588 x X2
       grind)
    | exact superpose eq13588 eq20475
    | exact resolve eq20475 eq13588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20475
  have eq20704 : ∀ X0 X1 X2 X3 X4 : G, x = (M.op (M.op (M.op X0 X1) X2) (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20604 X0 X1 X2 X3 X4
       have i₂ := eq12958
       grind)
    | exact superpose eq12958 eq20604
    | exact resolve eq20604 eq12958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20604
  have eq20798 : ∀ X3 X4 : G, x = (M.op x (M.op X3 X4)) := by
    intro X3 X4
    first
    | (have i₁ := eq20704 x x x X3 X4
       have i₂ := eq13591 (M.op x x) x (M.op X3 X4)
       grind)
    | exact superpose eq13591 eq20704
    | exact resolve eq20704 eq13591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20704
  have eq22487 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X1 X2)) X0) = (M.op (σ x) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq539 (σ x) (σ x) X0 X2 X1
       have i₂ := eq12957
       grind)
    | exact superpose eq12957 eq539
    | exact resolve eq539 eq12957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq22499 : ∀ X0 : G, (M.op x X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq22487 X0 x x
       have i₂ := eq13591 x (M.op x x) X0
       grind)
    | exact superpose eq13591 eq22487
    | exact resolve eq22487 eq13591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22487
  have eq27397 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq22499 (σ y)
       grind)
    | exact superpose eq22499 eq14
    | exact resolve eq14 eq22499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22499
  have eq41443 : ∀ X0 : G, (τ (M.op x (σ X0))) = (k (τ (M.op x (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq26 (M.op x (σ X0)) X0
       have i₂ := eq13596 (σ X0)
       grind)
    | exact superpose eq13596 eq26
    | exact resolve eq26 eq13596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq13596
  have eq109856 : ∀ X0 X1 X2 X3 X4 : G, (M.op (σ X0) (M.op (M.op X1 X2) (σ X0))) = (σ (k (k X3 X0) X0)) ∨ (k X4 (σ X0)) = X4 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq94 X0 (k X3 X0) X4
       have i₂ := eq1214 X3 X0 X1 X2
       grind)
    | exact superpose eq1214 eq94
    | (have j0 := eq94 X0 X1 X4
       have j1 := eq1214 X0 X0 X2 X3
       grind)
    | exact resolve eq94 eq1214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq1214
  have eq110289 : ∀ X0 X1 X2 X3 X4 : G, (M.op (σ X0) (M.op (M.op X1 X2) (σ X0))) = (σ (k (k X3 X0) X0)) ∨ (k X4 (σ X0)) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq109856 X0 X1 X2 X3 X4
       have j1 := eq11 X4 (σ X0)
       grind)
    | (have r₁ := eq109856 X0 X1 X2 X3 X4
       have r₂ := eq11 X0 (σ X0)
       grind)
    | exact resolve eq109856 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109856
  have eq110399 : ∀ X0 X3 X4 : G, (M.op (σ X0) (M.op x (σ X0))) = (σ (k (k X3 X0) X0)) ∨ (k X4 (σ X0)) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq110289 X0 x x X3 X4
       have i₂ := eq13591 x x (σ X0)
       grind)
    | exact superpose eq13591 eq110289
    | (have j0 := eq110289 X0 x x X3 X4
       grind)
    | exact resolve eq110289 eq13591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13591 eq110289
  have eq110491 : ∀ X0 X3 X4 : G, (M.op x (σ X0)) = (σ (k (k X3 X0) X0)) ∨ (k X4 (σ X0)) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq110399 X0 X3 X4
       have i₂ := eq13602 (σ X0)
       grind)
    | exact superpose eq13602 eq110399
    | (have j0 := eq110399 X0 X3 X4
       grind)
    | exact resolve eq110399 eq13602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13602 eq110399
  have eq283717 : ∀ X0 X1 X2 : G, (M.op x (σ (τ X1))) = (σ (k (τ (k X0 X1)) (τ X1))) ∨ (k X2 (σ (τ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq110491 (τ X1) (τ X0) X2
       have i₂ := eq75 X1 X0
       grind)
    | exact superpose eq75 eq110491
    | (have j0 := eq110491 (τ X1) x X2
       grind)
    | exact resolve eq110491 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq110491
  have eq284171 : ∀ X0 X1 X2 : G, (M.op x (σ (τ X1))) = (k (σ (τ (k X0 X1))) X1) ∨ (k X2 (σ (τ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq283717 X0 X1 X2
       have i₂ := eq16 X1 (τ (k X0 X1))
       grind)
    | exact superpose eq16 eq283717
    | (have j0 := eq283717 X0 X1 X2
       grind)
    | exact resolve eq283717 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq283717
  have eq284199 : ∀ X0 X1 X2 : G, (k (k X0 X1) X1) = (M.op x (σ (τ X1))) ∨ (k X2 (σ (τ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq284171 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq284171
    | (have j0 := eq284171 X0 X1 X2
       grind)
    | exact resolve eq284171 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284171
  have eq284214 : ∀ X0 X1 X2 : G, (k (k X0 X1) X1) = (M.op x X1) ∨ (k X2 (σ (τ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq284199 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq284199
    | (have j0 := eq284199 X0 X1 X2
       grind)
    | exact resolve eq284199 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284199
  have eq284222 : ∀ X0 X1 X2 : G, (k X2 X1) = X2 ∨ (k (k X0 X1) X1) = (M.op x X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq284214 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq284214
    | (have j0 := eq284214 X0 X1 X2
       grind)
    | exact resolve eq284214 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284214
  have eq415764 : ∀ X0 X1 : G, (M.op x X0) = (k (τ (M.op x (σ X0))) X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq284222 (τ (M.op x (σ X0))) X0 X1
       have i₂ := eq41443 X0
       grind)
    | exact superpose eq41443 eq284222
    | (have j0 := eq284222 X0 X0 X1
       grind)
    | exact resolve eq284222 eq41443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284222
  have eq415965 : ∀ X0 X1 : G, (M.op x X0) = (τ (M.op x (σ X0))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq415764 X0 X1
       have i₂ := eq41443 X0
       grind)
    | exact superpose eq41443 eq415764
    | (have j0 := eq415764 X0 X1
       grind)
    | exact resolve eq415764 eq41443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41443 eq415764
  have eq542452 : ∀ X0 X1 : G, (σ (M.op x X0)) = (M.op x (σ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op x (σ X0))
       have i₂ := eq415965 X0 X1
       grind)
    | exact superpose eq415965 eq10
    | (have j1 := eq415965 X0 X1
       grind)
    | exact resolve eq10 eq415965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415965
  have eq660730 : ∀ X0 : G, (M.op x (σ y)) ≠ (M.op x (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq27397
       have i₂ := eq542452 y X0
       grind)
    | exact superpose eq542452 eq27397
    | (have j1 := eq542452 y X0
       grind)
    | (have r₁ := eq27397
       have r₂ := eq542452 y x
       grind)
    | exact resolve eq27397 eq542452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27397 eq542452
  have eq660768 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq660730 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660730
  have eq661114 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq7127 y
       have i₂ := eq660768 y
       grind)
    | exact superpose eq660768 eq7127
    | (have j0 := eq7127 y
       grind)
    | (have r₁ := eq7127 y
       have r₂ := eq660768 y
       grind)
    | exact resolve eq7127 eq660768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7127 eq660768
  have eq661400 : y = (M.op y y) := by grind
  clear eq661114
  have eq664290 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq188 y X0 y
       have i₂ := eq661400
       grind)
    | exact superpose eq661400 eq188
    | exact resolve eq188 eq661400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq664417 : x = (M.op x y) := by
    first
    | (have i₁ := eq20798 y y
       have i₂ := eq661400
       grind)
    | exact superpose eq661400 eq20798
    | exact resolve eq20798 eq661400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20798
  have eq664571 : ∀ X0 : G, y = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq664290 X0
       have i₂ := eq661400
       grind)
    | exact superpose eq661400 eq664290
    | exact resolve eq664290 eq661400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661400 eq664290
  have eq664663 : y = (M.op x y) := by
    first
    | (have i₁ := eq664571 x
       have i₂ := eq13588 y x
       grind)
    | exact superpose eq13588 eq664571
    | exact resolve eq664571 eq13588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13588 eq664571
  have eq664729 : x = y := by
    first
    | (have i₁ := eq664663
       have i₂ := eq664417
       grind)
    | exact superpose eq664417 eq664663
    | exact resolve eq664663 eq664417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664417 eq664663
  have eq667430 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq664729
       grind)
    | exact superpose eq664729 eq14
    | exact resolve eq14 eq664729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664729
  have eq667437 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq667430
       have i₂ := eq12958
       grind)
    | exact superpose eq12958 eq667430
    | exact resolve eq667430 eq12958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12958 eq667430
  have eq667439 : False := by grind
  exact eq667439

/-- `Equation4416`: `x ◇ (x ◇ y) = (z ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation4416 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4416 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4416.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X0) X1) := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X2)) = (M.op X1 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 (M.op X1 X2) X3
       have i₂ := eq8 X1 X2 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X0)) X1) = (M.op (M.op X2 X0) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X2 X0) X1 X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 X3
       have i₂ := eq8 X1 X2 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 (M.op x X0)
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X2 (M.op X2 (M.op (M.op X1 X2) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op (M.op X1 X2) X3) X1
       have i₂ := eq8 (M.op X1 X2) X3 X0
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq35 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X0 X2) ∨ (M.op X0 X1) = (k X1 X0) := by
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
  have eq36 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X1) X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X1 X2
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq41 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq46 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X3) = (M.op (M.op X2 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 X2 X1 X3 (M.op x X0)
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq20
    | exact resolve eq20 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X2 X1) X3)) = (M.op (M.op X4 (M.op X2 X1)) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op X2 X1) X3 X4
       have i₂ := eq20 X2 X1 (M.op (M.op X2 X1) X3) X0
       grind)
    | (have i₁ := eq8 (M.op X2 X1) X3 X4
       have i₂ := eq20 X0 X1 (M.op (M.op X2 X1) X3) X2
       grind)
    | exact superpose eq20 eq8
    | exact resolve eq8 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq29
  have eq96 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq34 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq155 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X3 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 X2 (M.op X2 X0) X1 X3
       have i₂ := eq22 X2 X0 X1
       grind)
    | exact superpose eq22 eq20
    | exact resolve eq20 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq46
  have eq181 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq167 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq167
    | exact resolve eq167 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq203 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op X0 (M.op (M.op X4 X0) X2)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq18 X4 X0 X2 x
       have i₂ := eq18 X1 X0 X2 x
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op (M.op X1 X2) (M.op X2 (M.op X3 X2))) ∨ (k (M.op X3 X2) X0) = (M.op X0 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X3 X2 (M.op X3 X2) X1
       have i₂ := eq12 (M.op X3 X2) X0
       grind)
    | (have i₁ := eq18 X0 X1 X2 X3
       have i₂ := eq12 X0 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 (M.op X3 X2) X0
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op X0 (M.op X0 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 (M.op X0 X2) x
       have i₂ := eq18 X1 X0 X2 x
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq458 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X1 (M.op (M.op X0 X1) X1)) X3) ∨ (k X1 X2) = (M.op X2 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 X1 X2 X3
       have i₂ := eq36 X2 X1 X0
       grind)
    | exact superpose eq36 eq22
    | (have j1 := eq36 X2 X1 X2
       grind)
    | exact resolve eq22 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq508 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op X1 (M.op X1 X3)) ∨ (k X1 X2) = (M.op X2 X1) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq458 x X1 X2 X3
       have i₂ := eq155 X1 X3 (M.op x X1) X1
       grind)
    | exact superpose eq155 eq458
    | (have j0 := eq458 x X1 X2 X3
       grind)
    | exact resolve eq458 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458
  have eq588 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X4 (M.op X3 X1)) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20 X3 (M.op X3 X1) X2 X4
       have i₂ := eq63 X3 X1 X0 X2
       grind)
    | exact superpose eq63 eq20
    | exact resolve eq20 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq741 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X0 X1) (M.op X1 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X0 X1 X2
       have i₂ := eq19 X1 X2 X0 X0
       grind)
    | exact superpose eq19 eq22
    | exact resolve eq22 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq22
  have eq1112 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq155 X0 X2 X1 x
       have i₂ := eq23 x X1 X0 X2
       grind)
    | exact superpose eq23 eq155
    | exact resolve eq155 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1542 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq38 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq38
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1584 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq9
    | (have j1 := eq38 X1 X0
       grind)
    | exact resolve eq9 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1596 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq181 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq181
    | (have j1 := eq38 X0 X1
       grind)
    | exact resolve eq181 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq181
  have eq1625 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1596 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1596
    | (have j0 := eq1596 X0 X1
       grind)
    | exact resolve eq1596 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596
  have eq3201 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))) = (M.op (M.op X4 (M.op X5 X0)) (M.op (M.op X3 X0) X2)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq155 X0 (M.op (M.op X3 X0) X2) X5 X4
       have i₂ := eq203 X0 X3 X2 X1
       grind)
    | (have i₁ := eq155 X0 (M.op (M.op X3 X0) X2) X5 X4
       have i₂ := eq203 X0 X1 X2 X3
       grind)
    | exact superpose eq203 eq155
    | exact resolve eq155 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq3231 : ∀ X0 X2 X3 X4 X5 : G, (M.op X0 (M.op X0 X2)) = (M.op (M.op X4 (M.op X5 X0)) (M.op (M.op X3 X0) X2)) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq3201 X0 x X2 X3 X4 X5
       have i₂ := eq1112 X0 x X2
       grind)
    | exact superpose eq1112 eq3201
    | exact resolve eq3201 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3201
  have eq3482 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X0 X1)))) = (M.op (M.op X3 (M.op X4 X0)) (M.op (M.op X2 X0) X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq155 X0 (M.op (M.op X2 X0) X1) X4 X3
       have i₂ := eq234 X0 X2 X1
       grind)
    | exact superpose eq234 eq155
    | exact resolve eq155 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3488 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X0 (M.op X0 X1))) X3) = (M.op (M.op X4 (M.op X5 (M.op (M.op X2 X0) X1))) X3) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq588 X0 (M.op (M.op X2 X0) X1) X3 X5 X4
       have i₂ := eq234 X0 X2 X1
       grind)
    | exact superpose eq234 eq588
    | exact resolve eq588 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234 eq588
  have eq3643 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3482 X0 X1 x x x
       have i₂ := eq3231 X0 X1 x x x
       grind)
    | exact superpose eq3231 eq3482
    | exact resolve eq3482 eq3231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3231 eq3482
  have eq4185 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq741 X0 X0 X1
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq741
    | exact resolve eq741 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq4393 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq41 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq41
    | exact resolve eq41 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq4555 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4393 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq4393
    | (have j0 := eq4393 X0 X1
       grind)
    | exact resolve eq4393 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4393
  have eq4634 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq7299 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) X5) = (M.op (M.op X4 X3) (M.op (M.op X2 X3) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq80 X4 X3 X2 X5 (M.op x (M.op X1 X0))
       have i₂ := eq23 x X1 X0 (M.op X2 X3)
       grind)
    | exact superpose eq23 eq80
    | exact resolve eq80 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq80
  have eq7671 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X2 X3) X5) = (M.op (M.op X0 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq7299 X0 X1 X2 X3 x X5
       have i₂ := eq4185 X2 X3 X5 x
       grind)
    | exact superpose eq4185 eq7299
    | exact resolve eq7299 eq4185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4185 eq7299
  have eq7763 : ∀ X0 X2 X3 X5 : G, (M.op (M.op X2 X3) X5) = (M.op (M.op X0 (M.op X0 (M.op X0 (M.op X2 X3)))) X5) := by
    intro X0 X2 X3 X5
    first
    | (have i₁ := eq7671 X0 x X2 X3 X5
       have i₂ := eq3488 X0 (M.op X2 X3) x X5 X0 X0
       grind)
    | exact superpose eq3488 eq7671
    | exact resolve eq7671 eq3488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3488 eq7671
  have eq35854 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X2 X1) ∨ (M.op X2 X1) = (k (M.op X2 X1) X2) ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq96 (M.op X2 X1) X2
       have i₂ := eq508 X0 X2 X1
       grind)
    | (have i₁ := eq96 (M.op X1 x) X1
       have i₂ := eq508 X1 X2 x
       grind)
    | exact superpose eq508 eq96
    | (have j0 := eq96 (M.op X2 X1) X2
       have j1 := eq508 X0 X2 x
       grind)
    | exact resolve eq96 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq508
  have eq36401 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k (M.op X2 X1) X2) ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq35854 X0 X1 X2
       have j1 := eq35 X2 X0 X2
       grind)
    | (have r₁ := eq35854 X1 X2 X0
       have r₂ := eq35 X0 X1 X2
       grind)
    | exact resolve eq35854 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35854
  have eq39585 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1584 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1584
    | exact resolve eq1584 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39748 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq39585 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq39585
    | (have j0 := eq39585 X0 X1
       grind)
    | exact resolve eq39585 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq39585
  have eq51592 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq39748 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq39748
    | (have j0 := eq39748 X1 (τ X0)
       grind)
    | exact resolve eq39748 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39748
  have eq53948 : ∀ X0 X1 X2 : G, (k (τ X1) (τ X0)) = (τ (k X1 (M.op X2 X2))) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81 (M.op X2 X2) X1
       have i₂ := eq51592 X0 X2
       grind)
    | (have i₁ := eq81 X0 X1
       have i₂ := eq51592 X0 X1
       grind)
    | exact superpose eq51592 eq81
    | (have j1 := eq51592 X0 X2
       grind)
    | exact resolve eq81 eq51592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51592
  have eq53958 : ∀ X0 X1 X2 : G, (τ (k X1 X0)) = (τ (k X1 (M.op X2 X2))) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53948 X0 X1 X2
       have i₂ := eq81 X0 X1
       grind)
    | exact superpose eq81 eq53948
    | (have j0 := eq53948 X0 X1 X2
       grind)
    | exact resolve eq53948 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq53948
  have eq81471 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1542 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1542
    | (have j0 := eq1542 X1 (τ X0)
       grind)
    | exact resolve eq1542 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1542
  have eq81611 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq81471 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq81471
    | (have j0 := eq81471 X0 X1
       grind)
    | exact resolve eq81471 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq81471
  have eq81622 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq81611 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq81611
    | (have j0 := eq81611 X0 X1
       grind)
    | exact resolve eq81611 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81611
  have eq1284557 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k X0 (M.op X2 X2)) ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k X0 (M.op X2 X2))
       have i₂ := eq53958 X1 X0 X2
       grind)
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq53958 X0 X1 X2
       grind)
    | exact superpose eq53958 eq10
    | (have j1 := eq53958 X1 X1 X2
       grind)
    | exact resolve eq10 eq53958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53958
  have eq1284558 : ∀ X0 X1 X2 : G, (k X0 X1) = (k X0 (M.op X2 X2)) ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1284557 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq1284557
    | (have j0 := eq1284557 X0 X1 X2
       grind)
    | exact resolve eq1284557 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284557
  have eq1284633 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 (M.op X0 X0)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1284558 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284558
  have eq1284636 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq1284633
  have eq1284663 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1284636 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq1284636 X0 X1
       have i₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact superpose eq12 eq1284636
    | (have j0 := eq1284636 X1 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq1284636 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq1284636 (M.op X0 X0) X1
       have r₂ := eq12 X0 (M.op X1 (M.op X0 X0))
       grind)
    | exact resolve eq1284636 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1284712 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1284663 X0 X1
       have j1 := eq81622 X1 X0
       grind)
    | (have r₁ := eq1284663 (k X0 X1) (M.op X1 X0)
       have r₂ := eq81622 X0 X1
       grind)
    | (have r₁ := eq1284663 (M.op X1 X0) (k X0 X1)
       have r₂ := eq81622 X0 X1
       grind)
    | (have r₁ := eq1284663 (k X0 X0) X1
       have r₂ := eq81622 X0 X1
       grind)
    | exact resolve eq1284663 eq81622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81622 eq1284663
  have eq1284907 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq1284712
  have eq1284933 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1284907 X0
       have i₂ := eq8 X0 X0 X0
       grind)
    | exact superpose eq8 eq1284907
    | (have j0 := eq1284907 X0
       grind)
    | exact resolve eq1284907 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284907
  have eq1285071 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 X0 X0
       have i₂ := eq1284933 X0
       grind)
    | exact superpose eq1284933 eq35
    | (have j0 := eq35 X1 X0 x
       have j1 := eq1284933 X0
       grind)
    | exact resolve eq35 eq1284933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1284933
  have eq1285274 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1285071 X0 X1
       have j1 := eq1284636 X0 X1
       grind)
    | (have r₁ := eq1285071 X0 X1
       have r₂ := eq1284636 X0 X1
       grind)
    | exact resolve eq1285071 eq1284636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284636 eq1285071
  have eq1286220 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1285274 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285274
  have eq1286221 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1286220 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286220
  have eq1286430 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq1286221 (σ X0)
       grind)
    | exact superpose eq1286221 eq13
    | exact resolve eq13 eq1286221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1286468 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1286430 X0
       have i₂ := eq1286221 X0
       grind)
    | exact superpose eq1286221 eq1286430
    | exact resolve eq1286430 eq1286221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286221 eq1286430
  have eq1287055 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1584 X0 X1
       have i₂ := eq1286468 X0
       grind)
    | exact superpose eq1286468 eq1584
    | (have j0 := eq1584 X0 X1
       grind)
    | exact resolve eq1584 eq1286468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1584
  have eq1287123 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) (σ X0) X1
       have i₂ := eq1286468 X0
       grind)
    | exact superpose eq1286468 eq8
    | exact resolve eq8 eq1286468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1287129 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ X0)) X2) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X1 (σ X0) X2 (σ X0)
       have i₂ := eq1286468 X0
       grind)
    | exact superpose eq1286468 eq20
    | exact resolve eq20 eq1286468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1287290 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1287055 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq1287055
    | (have j0 := eq1287055 X0 X1
       grind)
    | exact resolve eq1287055 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287055
  have eq1294131 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1287290 y x
       grind)
    | exact superpose eq1287290 eq14
    | (have j1 := eq1287290 y x
       grind)
    | exact resolve eq14 eq1287290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1294156 : x = (M.op y y) := by
    first
    | (have j1 := eq4555 x y
       grind)
    | (have r₁ := eq1294131
       have r₂ := eq4555 x y
       grind)
    | exact resolve eq1294131 eq4555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4555 eq1294131
  have eq1294258 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op X0 (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1287129 y X0 X1
       have i₂ := eq1294156
       grind)
    | exact superpose eq1294156 eq1287129
    | exact resolve eq1287129 eq1294156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287129
  have eq1294261 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq8 y X0 y
       have i₂ := eq1294156
       grind)
    | exact superpose eq1294156 eq8
    | exact resolve eq8 eq1294156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1294345 : ∀ X0 X1 : G, (M.op X0 x) = (k x X0) ∨ (M.op y X0) = (M.op (M.op X1 y) (M.op y x)) := by
    intro X0 X1
    first
    | (have i₁ := eq226 X0 X1 y y
       have i₂ := eq1294156
       grind)
    | exact superpose eq1294156 eq226
    | exact resolve eq226 eq1294156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq1294637 : (M.op y x) = (M.op y (M.op y (M.op y x))) := by
    first
    | (have i₁ := eq3643 y y
       have i₂ := eq1294156
       grind)
    | exact superpose eq1294156 eq3643
    | exact resolve eq3643 eq1294156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3643
  have eq1294697 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X1 (M.op X1 (M.op X1 x))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq7763 X0 y y x
       have i₂ := eq1294156
       grind)
    | exact superpose eq1294156 eq7763
    | exact resolve eq7763 eq1294156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7763
  have eq1294769 : ∀ X0 : G, x = (k x y) ∨ (M.op y X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq36401 X0 y y
       have i₂ := eq1294156
       grind)
    | exact superpose eq1294156 eq36401
    | (have j0 := eq36401 X0 x y
       grind)
    | exact resolve eq36401 eq1294156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36401
  have eq1294882 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X1 x) (M.op (M.op X1 x) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1294697 X0 X1
       have i₂ := eq155 (M.op X1 x) X0 X1 X1
       grind)
    | exact superpose eq155 eq1294697
    | exact resolve eq1294697 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq1294697
  have eq1295134 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y (M.op y x))) ∨ (M.op X0 x) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq1294345 X0 x
       have i₂ := eq8 y (M.op y x) x
       grind)
    | exact superpose eq8 eq1294345
    | (have j0 := eq1294345 X0 x
       grind)
    | exact resolve eq1294345 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294345
  have eq1295291 : ∀ X0 X1 : G, (M.op x X0) = (M.op x (M.op x (M.op (M.op X1 x) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1294882 X0 X1
       have i₂ := eq8 x (M.op (M.op X1 x) X0) X1
       grind)
    | exact superpose eq8 eq1294882
    | exact resolve eq1294882 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294882
  have eq1295466 : ∀ X0 : G, (M.op X0 x) = (k x X0) ∨ (M.op y X0) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq1295134 X0
       have i₂ := eq1294637
       grind)
    | exact superpose eq1294637 eq1295134
    | (have j0 := eq1295134 X0
       grind)
    | exact resolve eq1295134 eq1294637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294637 eq1295134
  have eq1295588 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1295291 X0 x
       have i₂ := eq1112 x x X0
       grind)
    | exact superpose eq1112 eq1295291
    | exact resolve eq1295291 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112 eq1295291
  have eq1295936 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1294261 y
       have i₂ := eq1294156
       grind)
    | exact superpose eq1294156 eq1294261
    | exact resolve eq1294261 eq1294156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294261
  have eq1305881 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq1287123 y x
       have i₂ := eq1294258 x (σ y)
       grind)
    | exact superpose eq1294258 eq1287123
    | exact resolve eq1287123 eq1294258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287123 eq1294258
  have eq1306324 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1305881
       have i₂ := eq1294156
       grind)
    | exact superpose eq1294156 eq1305881
    | exact resolve eq1305881 eq1294156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1305881
  have eq1314096 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1625 y x
       have i₂ := eq1306324
       grind)
    | exact superpose eq1306324 eq1625
    | (have j0 := eq1625 y x
       grind)
    | exact resolve eq1625 eq1306324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625
  have eq1314103 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1287290 x y
       have i₂ := eq1306324
       grind)
    | exact superpose eq1306324 eq1287290
    | (have j0 := eq1287290 x y
       grind)
    | exact resolve eq1287290 eq1306324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287290 eq1306324
  have eq1325312 : ∀ X0 : G, x = (M.op y x) ∨ (M.op y X0) = (k X0 y) ∨ (M.op y y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq1294769 X0
       have i₂ := eq1295466 y
       grind)
    | exact superpose eq1295466 eq1294769
    | (have j0 := eq1294769 X0
       have j1 := eq1295466 y
       grind)
    | exact resolve eq1294769 eq1295466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294769 eq1295466
  have eq1325318 : ∀ X0 : G, x = (M.op x y) ∨ (M.op y X0) = (k X0 y) ∨ (M.op y y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq1325312 X0
       have i₂ := eq1295936
       grind)
    | exact superpose eq1295936 eq1325312
    | (have j0 := eq1325312 X0
       grind)
    | exact resolve eq1325312 eq1295936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325312
  have eq1325320 : ∀ X0 : G, (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (M.op y X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq1325318 X0
       have i₂ := eq1295936
       grind)
    | exact superpose eq1295936 eq1325318
    | (have j0 := eq1325318 X0
       grind)
    | exact resolve eq1325318 eq1295936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325318
  have eq1325322 : ∀ X0 : G, x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op y X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq1325320 X0
       have i₂ := eq1294156
       grind)
    | exact superpose eq1294156 eq1325320
    | (have j0 := eq1325320 X0
       grind)
    | exact resolve eq1325320 eq1294156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294156 eq1325320
  have eq1325323 : ∀ X0 : G, (M.op y X0) = (k X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1325322 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325322
  have eq1338931 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1314096
       grind)
    | exact superpose eq1314096 eq14
    | exact resolve eq14 eq1314096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314096
  have eq1338969 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1338931
       have i₂ := eq1325323 x
       grind)
    | exact superpose eq1325323 eq1338931
    | exact resolve eq1338931 eq1325323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325323
  have eq1338976 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1338931
       have i₂ := eq4634 y x
       grind)
    | exact superpose eq4634 eq1338931
    | (have j1 := eq4634 y x
       grind)
    | exact resolve eq1338931 eq4634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4634 eq1338931
  have eq1338978 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (k x y) := by grind
  clear eq1338976
  have eq1338987 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1338978
       have i₂ := eq1295936
       grind)
    | exact superpose eq1295936 eq1338978
    | exact resolve eq1338978 eq1295936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1338978
  have eq1338988 : x = (k x y) := by grind
  clear eq1338987
  have eq1338999 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1338969
       have i₂ := eq1295936
       grind)
    | exact superpose eq1295936 eq1338969
    | exact resolve eq1338969 eq1295936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1338969
  have eq1339000 : x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq1338999
  have eq1339010 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1339000
       have i₂ := eq1295936
       grind)
    | exact superpose eq1295936 eq1339000
    | exact resolve eq1339000 eq1295936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295936 eq1339000
  have eq1339011 : x = (M.op x y) := by grind
  clear eq1339010
  have eq1339256 : x = (M.op x x) := by
    first
    | (have i₁ := eq1295588 y
       have i₂ := eq1339011
       grind)
    | exact superpose eq1339011 eq1295588
    | exact resolve eq1295588 eq1339011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295588
  have eq1399738 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1314103
       grind)
    | exact superpose eq1314103 eq14
    | exact resolve eq14 eq1314103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314103
  have eq1399768 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1399738
       have i₂ := eq1338988
       grind)
    | exact superpose eq1338988 eq1399738
    | exact resolve eq1399738 eq1338988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1338988 eq1399738
  have eq1399774 : (σ x) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1399768
       have i₂ := eq1339011
       grind)
    | exact superpose eq1339011 eq1399768
    | exact resolve eq1399768 eq1339011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339011 eq1399768
  have eq1399775 : y = (M.op x x) := by grind
  clear eq1399774
  have eq1399780 : x = y := by
    first
    | (have i₁ := eq1399775
       have i₂ := eq1339256
       grind)
    | exact superpose eq1339256 eq1399775
    | exact resolve eq1399775 eq1339256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339256 eq1399775
  have eq1399787 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1399780
       grind)
    | exact superpose eq1399780 eq14
    | exact resolve eq14 eq1399780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399780
  have eq1400195 : False := by grind
  exact eq1400195

/-- `Equation4417`: `x ◇ (x ◇ y) = (z ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_y_pxx_pxy_Equation4417 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4417 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4417.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X0) X2) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq21 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X1) X3) = (M.op X1 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 (M.op X1 x) X3
       have i₂ := eq8 X1 x X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X3 X1) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 x X3
       have i₂ := eq8 X1 x X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X2 X0)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X0 X2 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq37 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq47 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
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
  clear eq15
  have eq164 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) ≠ (M.op (M.op X2 X1) X2) ∨ (M.op X1 X1) = (k X1 (M.op (M.op X2 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 (M.op (M.op X2 X1) X2)
       have i₂ := eq21 X2 X1 X0
       grind)
    | exact superpose eq21 eq11
    | (have j0 := eq11 X1 (M.op (M.op X2 X1) X2)
       grind)
    | (have r₁ := eq11 (M.op (M.op X1 (M.op (M.op X0 X1) X0)) X1) (M.op X1 (M.op (M.op X0 X1) X0))
       have r₂ := eq21 X0 X1 (M.op X1 (M.op (M.op X0 X1) X0))
       grind)
    | (have r₁ := eq11 X1 (M.op (M.op x X1) x)
       have r₂ := eq21 x X1 x
       grind)
    | exact resolve eq11 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op (M.op X2 (M.op (M.op X3 X1) X3)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X2 (M.op (M.op X3 X1) X3) X1
       have i₂ := eq21 X3 X1 X0
       grind)
    | exact superpose eq21 eq23
    | exact resolve eq23 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq169 : ∀ X1 X2 : G, (M.op X1 X1) = (k X1 (M.op (M.op X2 X1) X2)) := by
    intro X1 X2
    first
    | (have j0 := eq164 x X1 X2
       grind)
    | (have r₁ := eq164 x X1 x
       have r₂ := eq23 x X1 x
       grind)
    | (have r₁ := eq164 x X1 x
       have r₂ := eq23 x X1 x
       grind)
    | exact resolve eq164 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq164
  have eq195 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X3 X4)) = (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X0)) (M.op X3 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq25 X2 x X3 X4
       have i₂ := eq25 X0 X1 X2 x
       grind)
    | (have i₁ := eq25 (M.op X0 (M.op X0 X1)) X0 X2 X3
       have i₂ := eq25 X0 X1 (M.op X0 (M.op X0 X1)) X3
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq252 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq169 X0 x
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq169
    | exact resolve eq169 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 X1 : G, (k X0 (τ (M.op (M.op X1 (σ X0)) X1))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 (M.op (M.op X1 (σ X0)) X1)
       have i₂ := eq169 (σ X0) X1
       grind)
    | exact superpose eq169 eq32
    | exact resolve eq32 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq169
  have eq637 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq46 x y
       grind)
    | exact superpose eq46 eq14
    | (have j1 := eq46 x y
       grind)
    | exact resolve eq14 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq640 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq46 X0 X1
       grind)
    | exact superpose eq46 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       have j1 := eq46 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq46 X0 X1
       grind)
    | exact resolve eq11 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq663 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq640 X0 X1
       have j1 := eq11 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq640 X0 X1
       have r₂ := eq11 (σ X0) (σ X1)
       grind)
    | exact resolve eq640 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq666 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq663 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq663
    | (have j0 := eq663 X0 X1
       grind)
    | exact resolve eq663 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq2153 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq661 (τ X0) (τ X1)
       have i₂ := eq37 X1 X0
       grind)
    | exact superpose eq37 eq661
    | (have j0 := eq661 (τ X0) (τ X1)
       grind)
    | exact resolve eq661 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq2160 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2153 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq2153
    | (have j0 := eq2153 X0 X1
       grind)
    | exact resolve eq2153 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2153
  have eq2162 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2160 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2160
    | (have j0 := eq2160 X0 X1
       grind)
    | exact resolve eq2160 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2160
  have eq2163 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2162 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2162
    | (have j0 := eq2162 X0 X1
       grind)
    | exact resolve eq2162 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2162
  have eq2164 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2163 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2163
    | (have j0 := eq2163 X0 X1
       grind)
    | exact resolve eq2163 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2163
  have eq2165 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq47
    | exact resolve eq47 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq2200 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2165 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2165
    | (have j0 := eq2165 X0 X1
       grind)
    | exact resolve eq2165 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2165
  have eq2208 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2164 (τ X0) (τ X1)
       have i₂ := eq37 X1 X0
       grind)
    | exact superpose eq37 eq2164
    | (have j0 := eq2164 (τ X0) (τ X1)
       grind)
    | exact resolve eq2164 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2164
  have eq9765 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq637
       have i₂ := eq2200 x y
       grind)
    | exact superpose eq2200 eq637
    | (have j1 := eq2200 (σ x) (σ y)
       grind)
    | (have r₁ := eq637
       have r₂ := eq2200 x y
       grind)
    | exact resolve eq637 eq2200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637 eq2200
  have eq9766 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq9765
  have eq9779 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq666 (τ X1) (τ X0)
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq666
    | exact resolve eq666 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq9787 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9779 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq9779
    | (have j0 := eq9779 X0 X1
       grind)
    | exact resolve eq9779 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9779
  have eq9788 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9787 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq9787
    | (have j0 := eq9787 X0 X1
       grind)
    | exact resolve eq9787 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9787
  have eq9789 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9788 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9788
    | (have j0 := eq9788 X0 X1
       grind)
    | exact resolve eq9788 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9788
  have eq9790 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9789 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq9789
    | (have j0 := eq9789 X0 X1
       grind)
    | exact resolve eq9789 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9789
  have eq17300 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X2 X3) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq166 X2 X3 (M.op X0 (M.op X0 X3)) X0
       have i₂ := eq195 X0 X3 (M.op X0 X3) X0 X1
       grind)
    | exact superpose eq195 eq166
    | exact resolve eq166 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166 eq195
  have eq17775 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17300 X0 X1 x x
       have i₂ := eq17300 X2 X3 x x
       grind)
    | exact superpose eq17300 eq17300
    | exact resolve eq17300 eq17300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19189 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq17775 X2 X3 X4 (M.op X4 x)
       have i₂ := eq17775 X4 x X0 X1
       grind)
    | (have i₁ := eq17775 X2 X3 X4 (M.op X4 x)
       have i₂ := eq17775 X0 X1 X4 x
       grind)
    | exact superpose eq17775 eq17775
    | exact resolve eq17775 eq17775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19268 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq17775 X0 X1 (σ x) (σ y)
       have i₂ := eq9766
       grind)
    | exact superpose eq9766 eq17775
    | exact resolve eq17775 eq9766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19514 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X4 X2) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq8 X2 x X4
       have i₂ := eq17775 X2 x X0 X1
       grind)
    | (have i₁ := eq8 X2 x X4
       have i₂ := eq17775 X0 X1 X2 x
       grind)
    | exact superpose eq17775 eq8
    | exact resolve eq8 eq17775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20770 : ∀ X0 X1 X2 X4 X5 : G, (M.op X2 (M.op X0 (M.op X0 X1))) = (M.op (M.op X4 X5) X4) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq19514 X2 (M.op X2 x) X5 X4
       have i₂ := eq17775 X2 x X0 X1
       grind)
    | (have i₁ := eq19514 X2 (M.op X2 x) X5 X4
       have i₂ := eq17775 X0 X1 X2 x
       grind)
    | exact superpose eq17775 eq19514
    | exact resolve eq19514 eq17775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20907 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X0) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq19514 X2 X3 (M.op X4 x) X4
       have i₂ := eq19514 X4 x X1 X0
       grind)
    | exact superpose eq19514 eq19514
    | exact resolve eq19514 eq19514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21032 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X4 X2) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq8 X2 x X4
       have i₂ := eq19514 X2 x X1 X0
       grind)
    | exact superpose eq19514 eq8
    | exact resolve eq8 eq19514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21061 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X2 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq252 X2 x
       have i₂ := eq19514 X2 x X1 X0
       grind)
    | exact superpose eq19514 eq252
    | exact resolve eq252 eq19514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq21294 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq17300 X2 X3 x X5
       have i₂ := eq19514 X0 X1 X5 x
       grind)
    | exact superpose eq19514 eq17300
    | exact resolve eq17300 eq19514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17300
  have eq21318 : ∀ X0 X1 X2 : G, (τ (M.op (σ X2) (σ X2))) = (k X2 (τ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq254 X2 x
       have i₂ := eq19514 X0 X1 (σ X2) x
       grind)
    | exact superpose eq19514 eq254
    | exact resolve eq254 eq19514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq25560 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X4) X3) = (M.op (k X0 (M.op (M.op X1 X2) X1)) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq21032 X3 X4 X0 X0
       have i₂ := eq21061 X1 X2 X0
       grind)
    | exact superpose eq21061 eq21032
    | exact resolve eq21032 eq21061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21061
  have eq41341 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 (M.op X3 (M.op X3 X4))) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq20770 X3 X4 X2 X5 (M.op x (M.op x x))
       have i₂ := eq19189 x x X0 X1 X5
       grind)
    | (have i₁ := eq20770 X0 X1 X2 X2 (M.op X2 X3)
       have i₂ := eq19189 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq19189 eq20770
    | exact resolve eq20770 eq19189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19189 eq20770
  have eq46562 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X4) X3) = (M.op (M.op (M.op (M.op X0 X1) X0) X2) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq21032 X3 X4 (M.op X5 x) X5
       have i₂ := eq20907 X0 X1 X5 x X2
       grind)
    | (have i₁ := eq21032 X0 X1 X4 (M.op (M.op X0 X1) X0)
       have i₂ := eq20907 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq20907 eq21032
    | exact resolve eq21032 eq20907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63390 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X4) X3) = (M.op (M.op (M.op X0 (M.op X0 X1)) X2) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq21032 X3 X4 (M.op X5 x) X5
       have i₂ := eq21294 X0 X1 X5 x X2
       grind)
    | (have i₁ := eq21032 X0 X1 X5 (M.op X0 (M.op X0 X1))
       have i₂ := eq21294 X0 X1 X2 X3 X5
       grind)
    | exact superpose eq21294 eq21032
    | exact resolve eq21032 eq21294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21294
  have eq275746 : ∀ X0 X1 X2 : G, (τ (M.op (σ (τ X0)) (σ (τ X0)))) = (τ (k X0 (M.op X1 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq37 (M.op X1 (M.op X1 X2)) X0
       have i₂ := eq21318 X1 X2 (τ X0)
       grind)
    | exact superpose eq21318 eq37
    | exact resolve eq37 eq21318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq21318
  have eq275751 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) = (τ (k X0 (M.op X1 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq275746 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq275746
    | exact resolve eq275746 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275746
  have eq277440 : ∀ X0 X1 X2 X3 : G, (τ (M.op X3 X3)) = (τ (k X3 (M.op (M.op (M.op X0 X1) X0) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq275751 X3 x x
       have i₂ := eq20907 X0 X1 x x X2
       grind)
    | (have i₁ := eq275751 X0 (M.op (M.op X0 X1) X0) X2
       have i₂ := eq20907 X0 X1 X2 X3 (M.op (M.op (M.op X0 X1) X0) X2)
       grind)
    | exact superpose eq20907 eq275751
    | exact resolve eq275751 eq20907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20907 eq275751
  have eq664230 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq9766
       have i₂ := eq19268 X0 X1
       grind)
    | exact superpose eq19268 eq9766
    | exact resolve eq9766 eq19268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9766 eq19268
  have eq664240 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq664230 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664230
  have eq664448 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq664240 X0 (M.op X0 x)
       have i₂ := eq664240 X0 x
       grind)
    | exact superpose eq664240 eq664240
    | exact resolve eq664240 eq664240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665356 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (k X0 (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq277440 x x (M.op (M.op (M.op x x) x) x) X0
       have i₂ := eq664240 (M.op (M.op x x) x) x
       grind)
    | exact superpose eq664240 eq277440
    | exact resolve eq277440 eq664240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277440
  have eq665370 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 X1) X0) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq46562 x x x X0 X1 (M.op (M.op (M.op (M.op x x) x) x) x)
       have i₂ := eq664240 (M.op (M.op (M.op x x) x) x) x
       grind)
    | exact superpose eq664240 eq46562
    | exact resolve eq46562 eq664240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664240
  have eq665375 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq664448 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664448
  have eq665376 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq665356 X0
       have i₂ := eq20 X0 y
       grind)
    | exact superpose eq20 eq665356
    | exact resolve eq665356 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq665356
  have eq668474 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq665370 X0 (σ y)
       have i₂ := eq665375 X0
       grind)
    | exact superpose eq665375 eq665370
    | exact resolve eq665370 eq665375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669230 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq668474 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668474
  have eq672898 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq665376 (σ y)
       have i₂ := eq669230 (σ y)
       grind)
    | exact superpose eq669230 eq665376
    | exact resolve eq665376 eq669230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665376 eq669230
  have eq672912 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op x y) := by grind
  clear eq672898
  have eq672919 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq672912
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq672912
    | exact resolve eq672912 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672912
  have eq674084 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9790 y y
       have i₂ := eq672919
       grind)
    | exact superpose eq672919 eq9790
    | (have r₁ := eq9790 y y
       have r₂ := eq672919
       grind)
    | exact resolve eq9790 eq672919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9790 eq672919
  have eq674088 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq674084
  have eq675097 : (σ y) = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq665370 y y
       have i₂ := eq674088
       grind)
    | exact superpose eq674088 eq665370
    | exact resolve eq665370 eq674088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665370
  have eq675098 : (σ y) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq675097
  have eq675928 : y = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq674088
       have i₂ := eq675098
       grind)
    | exact superpose eq675098 eq674088
    | exact resolve eq674088 eq675098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674088 eq675098
  have eq676187 : y = (M.op x y) ∨ y = (σ y) := by grind
  clear eq675928
  have eq676605 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x y) ∨ y = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq17775 X0 X1 x y
       have i₂ := eq676187
       grind)
    | exact superpose eq676187 eq17775
    | exact resolve eq17775 eq676187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17775
  have eq676657 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op y x) ∨ y = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq21032 X0 X1 y x
       have i₂ := eq676187
       grind)
    | exact superpose eq676187 eq21032
    | exact resolve eq21032 eq676187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698743 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ y = (σ y) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq676605 X0 (M.op X0 x)
       have i₂ := eq676605 X0 x
       grind)
    | exact superpose eq676605 eq676605
    | exact resolve eq676605 eq676605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699753 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) X0) ∨ y = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq46562 x x x X0 X1 (M.op (M.op (M.op (M.op x x) x) x) x)
       have i₂ := eq676605 (M.op (M.op (M.op x x) x) x) x
       grind)
    | exact superpose eq676605 eq46562
    | exact resolve eq46562 eq676605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46562 eq676605
  have eq699757 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ y = (σ y) := by
    intro X0
    first
    | (have j0 := eq698743 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698743
  have eq721126 : y = (M.op y x) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq699753 x y
       have i₂ := eq676187
       grind)
    | exact superpose eq676187 eq699753
    | exact resolve eq699753 eq676187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699753
  have eq721982 : y = (M.op y x) ∨ y = (σ y) := by grind
  clear eq721126
  have eq723359 : y = (M.op y y) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq676657 y x
       have i₂ := eq721982
       grind)
    | exact superpose eq721982 eq676657
    | exact resolve eq676657 eq721982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676657 eq721982
  have eq723365 : y = (M.op y y) ∨ y = (σ y) := by grind
  clear eq723359
  have eq724547 : y ≠ y ∨ y = (k y y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq723365
       grind)
    | exact superpose eq723365 eq11
    | (have r₁ := eq11 y y
       have r₂ := eq723365
       grind)
    | exact resolve eq11 eq723365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723365
  have eq724904 : y = (k y y) ∨ y = (σ y) := by grind
  clear eq724547
  have eq725589 : (τ y) ≠ (τ y) ∨ (τ y) = (M.op (τ y) (τ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq2208 y y
       have i₂ := eq724904
       grind)
    | exact superpose eq724904 eq2208
    | (have j0 := eq2208 y y
       grind)
    | exact resolve eq2208 eq724904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2208 eq724904
  have eq725596 : (τ y) = (M.op (τ y) (τ y)) ∨ y = (σ y) := by grind
  clear eq725589
  have eq742431 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (σ y) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq699757 X0
       have i₂ := eq676187
       grind)
    | exact superpose eq676187 eq699757
    | exact resolve eq699757 eq676187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676187 eq699757
  have eq743546 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (σ y) := by
    intro X0
    first
    | (have j0 := eq742431 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742431
  have eq745621 : ∀ X0 X1 : G, y = (M.op (M.op X0 X1) X0) ∨ y = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq25560 y x x X0 X1
       have i₂ := eq743546 (k y (M.op (M.op x x) x))
       grind)
    | exact superpose eq743546 eq25560
    | exact resolve eq25560 eq743546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25560 eq743546
  have eq747132 : y = (M.op (τ y) (τ y)) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq745621 (τ y) (τ y)
       have i₂ := eq725596
       grind)
    | exact superpose eq725596 eq745621
    | exact resolve eq745621 eq725596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745621
  have eq748489 : y = (M.op (τ y) (τ y)) ∨ y = (σ y) := by grind
  clear eq747132
  have eq799861 : y = (τ y) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq725596
       have i₂ := eq748489
       grind)
    | exact superpose eq748489 eq725596
    | exact resolve eq725596 eq748489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725596 eq748489
  have eq800157 : y = (τ y) ∨ y = (σ y) := by grind
  clear eq799861
  have eq801294 : y = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq800157
       grind)
    | exact superpose eq800157 eq10
    | exact resolve eq10 eq800157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800157
  have eq801301 : y = (σ y) := by grind
  clear eq801294
  have eq802302 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq801301
       grind)
    | exact superpose eq801301 eq14
    | exact resolve eq14 eq801301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq802306 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq665375 X0
       have i₂ := eq801301
       grind)
    | exact superpose eq801301 eq665375
    | exact resolve eq665375 eq801301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665375
  have eq813904 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq802306 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802306
  have eq813905 : y = (M.op x y) := by grind
  clear eq813904
  have eq814460 : ∀ X0 : G, (M.op x y) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq26 x X0 y
       have i₂ := eq813905
       grind)
    | exact superpose eq813905 eq26
    | exact resolve eq26 eq813905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq814847 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq19514 X0 X1 y x
       have i₂ := eq813905
       grind)
    | exact superpose eq813905 eq19514
    | exact resolve eq19514 eq813905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19514
  have eq814882 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq21032 X0 X1 y x
       have i₂ := eq813905
       grind)
    | exact superpose eq813905 eq21032
    | exact resolve eq21032 eq813905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21032
  have eq814997 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X1 X2)) X3) = (M.op X0 (M.op x y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq41341 X1 X2 X0 x y X3
       have i₂ := eq813905
       grind)
    | exact superpose eq813905 eq41341
    | exact resolve eq41341 eq813905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41341
  have eq815027 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op x y) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63390 x y X2 X0 X1 X3
       have i₂ := eq813905
       grind)
    | exact superpose eq813905 eq63390
    | exact resolve eq63390 eq813905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63390
  have eq815062 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op y X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq815027 X0 X1 X2 X3
       have i₂ := eq813905
       grind)
    | exact superpose eq813905 eq815027
    | exact resolve eq815027 eq813905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815027
  have eq815072 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X1 X2)) X3) = (M.op X0 y) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq814997 X0 X1 X2 X3
       have i₂ := eq813905
       grind)
    | exact superpose eq813905 eq814997
    | exact resolve eq814997 eq813905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814997
  have eq815156 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq814460 x
       have i₂ := eq814847 x x
       grind)
    | exact superpose eq814847 eq814460
    | exact resolve eq814460 eq814847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814460
  have eq815162 : ∀ X2 X3 : G, (M.op y x) = (M.op (M.op y X2) X3) := by
    intro X2 X3
    first
    | (have i₁ := eq815062 x x X2 X3
       have i₂ := eq814882 x x
       grind)
    | exact superpose eq814882 eq815062
    | exact resolve eq815062 eq814882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814882 eq815062
  have eq815170 : ∀ X0 X3 : G, (M.op X0 y) = (M.op (M.op y x) X3) := by
    intro X0 X3
    first
    | (have i₁ := eq815072 X0 x x X3
       have i₂ := eq814847 x x
       grind)
    | exact superpose eq814847 eq815072
    | exact resolve eq815072 eq814847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814847 eq815072
  have eq815214 : y = (M.op y x) := by
    first
    | (have i₁ := eq815156
       have i₂ := eq813905
       grind)
    | exact superpose eq813905 eq815156
    | exact resolve eq815156 eq813905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813905 eq815156
  have eq815220 : ∀ X0 : G, (M.op X0 y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq815170 X0 x
       have i₂ := eq815162 x x
       grind)
    | exact superpose eq815162 eq815170
    | exact resolve eq815170 eq815162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815162 eq815170
  have eq815243 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq815220 X0
       have i₂ := eq815214
       grind)
    | exact superpose eq815214 eq815220
    | exact resolve eq815220 eq815214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815214 eq815220
  have eq822047 : (σ y) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq802302
       have i₂ := eq815243 x
       grind)
    | exact superpose eq815243 eq802302
    | exact resolve eq802302 eq815243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802302
  have eq822061 : y ≠ (σ y) := by
    first
    | (have i₁ := eq822047
       have i₂ := eq815243 (σ x)
       grind)
    | exact superpose eq815243 eq822047
    | exact resolve eq822047 eq815243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815243 eq822047
  have eq822713 : False := by grind
  exact eq822713

/-- `Equation4417`: `x ◇ (x ◇ y) = (z ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pyx_Equation4417 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4417 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4417.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X0) X2) := by
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
  have eq17 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X1) X3) = (M.op X1 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 (M.op X1 x) X3
       have i₂ := eq8 X1 x X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X3 X1) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 x X3
       have i₂ := eq8 X1 x X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op X0 X1) X0) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X1 X2) X3 X1
       have i₂ := eq8 X1 X2 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X0 X2 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq28 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
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
  have eq31 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq32 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 X0 X0
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq33 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq28 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op (M.op X2 (M.op X1 X3)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X2 (M.op X1 X3) X1
       have i₂ := eq8 X1 X3 X0
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op (M.op X0 X1) X0) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X2 X3 (M.op X3 X1)
       have i₂ := eq19 X3 X1 X0
       grind)
    | (have i₁ := eq19 X2 X3 (M.op X3 X1)
       have i₂ := eq19 X0 X1 X3
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X0 (M.op X0 X1)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X2 X3 (M.op X3 X0)
       have i₂ := eq8 X0 X1 X3
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X0) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X2 X1)
       have i₂ := eq19 X2 X1 X0
       grind)
    | (have i₁ := eq8 X2 X3 (M.op X2 X1)
       have i₂ := eq19 X0 X1 X2
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X3) = (M.op (M.op X2 X1) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X2 X1) X2 X3
       have i₂ := eq19 X2 X1 X0
       grind)
    | (have i₁ := eq8 (M.op X2 X1) X2 X3
       have i₂ := eq19 X0 X1 X2
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26
    | exact resolve eq26 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq101 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X3 (M.op X0 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X0 (M.op X0 X2) X3
       have i₂ := eq22 X0 X2 X1
       grind)
    | (have i₁ := eq19 X0 (M.op X0 X2) X3
       have i₂ := eq22 X0 X1 X2
       grind)
    | exact superpose eq22 eq19
    | exact resolve eq19 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 X2) (M.op (M.op X0 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X0 X2) X3 X0
       have i₂ := eq22 X0 X2 X1
       grind)
    | (have i₁ := eq8 (M.op X0 X2) X3 X0
       have i₂ := eq22 X0 X1 X2
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X2 (σ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq33 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq33 eq13
    | (have j1 := eq33 (σ X0) X2 X2
       grind)
    | exact resolve eq13 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq33 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq151 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X2 X1)) = (M.op X2 (M.op (M.op X3 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17 X3 X2 (M.op X2 X1)
       have i₂ := eq19 X2 X1 X0
       grind)
    | (have i₁ := eq17 X3 X2 (M.op X2 X1)
       have i₂ := eq19 X0 X1 X2
       grind)
    | exact superpose eq19 eq17
    | exact resolve eq17 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq887 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq11
    | (have j0 := eq11 X1 (σ X0)
       have j1 := eq31 X0 X1
       grind)
    | (have r₁ := eq11 X0 (σ X0)
       have r₂ := eq31 X0 X1
       grind)
    | exact resolve eq11 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq934 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq939 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq887 X0 X1
       have j1 := eq11 X1 (σ X0)
       grind)
    | (have r₁ := eq887 X0 X1
       have r₂ := eq11 X0 (σ X0)
       grind)
    | exact resolve eq887 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq955 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq939 (τ X0) X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq939
    | (have j0 := eq939 (τ X0) X1
       grind)
    | exact resolve eq939 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq959 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq955 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq955
    | (have j0 := eq955 X0 X1
       grind)
    | exact resolve eq955 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq963 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq959 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq959
    | (have j0 := eq959 X0 X1
       grind)
    | exact resolve eq959 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959
  have eq1017 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq963 (τ X0) X1
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq963
    | (have j0 := eq963 (τ X0) X1
       grind)
    | exact resolve eq963 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq963
  have eq1091 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq32
    | (have j0 := eq32 X1 X1
       grind)
    | exact resolve eq32 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq1146 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1091 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1091
    | (have j0 := eq1091 X0 X1
       grind)
    | exact resolve eq1091 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
  have eq2252 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq133 X0 X0
       have i₂ := eq1146 X1 X0
       grind)
    | exact superpose eq1146 eq133
    | (have j0 := eq133 X0 X0
       have j1 := eq1146 X1 X0
       grind)
    | (have r₁ := eq133 X1 X1
       have r₂ := eq1146 X0 X1
       grind)
    | exact resolve eq133 eq1146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq1146
  have eq2261 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2252 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2252
  have eq3448 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq939 X0 X1
       have i₂ := eq2261 X0 X2
       grind)
    | exact superpose eq2261 eq939
    | (have j0 := eq939 X0 X1
       have j1 := eq2261 X0 X2
       grind)
    | exact resolve eq939 eq2261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939 eq2261
  have eq3495 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3448 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3448
  have eq3885 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq934 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq934
    | (have j0 := eq934 (τ X0)
       grind)
    | exact resolve eq934 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq934
  have eq3901 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3885 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3885
    | (have j0 := eq3885 X0
       grind)
    | exact resolve eq3885 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3885
  have eq3908 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3901 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3901
    | (have j0 := eq3901 X0
       grind)
    | exact resolve eq3901 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3901
  have eq4296 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq128 x y X0
       grind)
    | exact superpose eq128 eq14
    | (have j1 := eq128 x x X0
       grind)
    | exact resolve eq14 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq4389 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq4296 X0
       have j1 := eq3495 x X0 x
       grind)
    | (have r₁ := eq4296 X0
       have r₂ := eq3495 x x y
       grind)
    | exact resolve eq4296 eq3495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3495 eq4296
  have eq4420 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3908 (σ x)
       have i₂ := eq4389 (σ x)
       grind)
    | exact superpose eq4389 eq3908
    | (have j0 := eq3908 (σ x)
       grind)
    | (have r₁ := eq3908 (σ x)
       have r₂ := eq4389 (σ x)
       grind)
    | exact resolve eq3908 eq4389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4422 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1017 (σ x) X0
       have i₂ := eq4389 (σ x)
       grind)
    | exact superpose eq4389 eq1017
    | (have j0 := eq1017 (σ x) X0
       grind)
    | exact resolve eq1017 eq4389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017 eq4389
  have eq4447 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 := by
    intro X0
    first
    | (have j0 := eq4422 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4422
  have eq4449 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4420
  have eq4457 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq4447 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq4447
    | exact resolve eq4447 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4447
  have eq4610 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3908 x
       have i₂ := eq4457 x
       grind)
    | exact superpose eq4457 eq3908
    | (have j0 := eq3908 x
       grind)
    | (have r₁ := eq3908 x
       have r₂ := eq4457 x
       grind)
    | exact resolve eq3908 eq4457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3908 eq4457
  have eq4636 : x = (M.op x x) := by grind
  clear eq4610
  have eq5004 : ∀ X0 : G, (M.op x x) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq22 x X0 x
       have i₂ := eq4636
       grind)
    | exact superpose eq4636 eq22
    | exact resolve eq22 eq4636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq5011 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x x) (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x x X0 X1
       have i₂ := eq4636
       grind)
    | exact superpose eq4636 eq55
    | exact resolve eq55 eq4636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq5013 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x x) (M.op X0 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 x x X0 X1
       have i₂ := eq4636
       grind)
    | exact superpose eq4636 eq63
    | exact resolve eq63 eq4636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5038 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op X0 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq5013 X0 X1
       have i₂ := eq4636
       grind)
    | exact superpose eq4636 eq5013
    | exact resolve eq5013 eq4636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5013
  have eq5039 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op x (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq5011 X0 X1
       have i₂ := eq4636
       grind)
    | exact superpose eq4636 eq5011
    | exact resolve eq5011 eq4636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5011
  have eq5042 : ∀ X0 : G, x = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq5004 X0
       have i₂ := eq4636
       grind)
    | exact superpose eq4636 eq5004
    | exact resolve eq5004 eq4636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4636 eq5004
  have eq5246 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X4) X3) = (M.op (M.op (M.op X0 X1) (M.op (M.op X0 X1) X2)) (M.op X4 (M.op X0 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq54 X0 (M.op X0 X5) X3 X4
       have i₂ := eq102 X0 X5 X1 X2
       grind)
    | exact superpose eq102 eq54
    | exact resolve eq54 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5303 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X0 X4)) X0) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op (M.op (M.op X0 X1) X2) X3)) (M.op (M.op X0 X1) (M.op (M.op X0 X1) X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq101 X0 X4 X1 (M.op (M.op X0 X1) (M.op (M.op X0 X1) X5))
       have i₂ := eq102 (M.op X0 X1) X5 X2 X3
       grind)
    | exact superpose eq102 eq101
    | exact resolve eq101 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq5304 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X4 X0) X4) X0) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op (M.op (M.op X0 X1) X2) X3)) (M.op (M.op X0 X1) (M.op (M.op X0 X1) X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq51 X4 X0 (M.op (M.op X0 X1) (M.op (M.op X0 X1) X5)) X1
       have i₂ := eq102 (M.op X0 X1) X5 X2 X3
       grind)
    | exact superpose eq102 eq51
    | exact resolve eq51 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq5311 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X2) (M.op (M.op X0 (M.op X0 X1)) X0)) = (M.op (M.op (M.op X4 X0) X4) X0) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq20 X4 X0 X2 (M.op (M.op X0 X2) x)
       have i₂ := eq102 X0 X1 X2 x
       grind)
    | exact superpose eq102 eq20
    | exact resolve eq20 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq102
  have eq5410 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op (M.op X0 (M.op X0 X1)) X0)) = (M.op (M.op x (M.op X0 x)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5311 X0 X1 X2 x
       have i₂ := eq5039 x X0
       grind)
    | exact superpose eq5039 eq5311
    | exact resolve eq5311 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5311
  have eq5413 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X4 X0) X4) X0) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op (M.op (M.op X0 X1) X2) X3)) (M.op x (M.op (M.op X0 X1) x))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5304 X0 X1 X2 X3 X4 x
       have i₂ := eq5038 (M.op X0 X1) x
       grind)
    | exact superpose eq5038 eq5304
    | exact resolve eq5304 eq5038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5304
  have eq5414 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X0 X4)) X0) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op (M.op (M.op X0 X1) X2) X3)) (M.op x (M.op (M.op X0 X1) x))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5303 X0 X1 X2 X3 X4 x
       have i₂ := eq5038 (M.op X0 X1) x
       grind)
    | exact superpose eq5038 eq5303
    | exact resolve eq5303 eq5038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5303
  have eq5449 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op X3 X4) X3) = (M.op (M.op x (M.op (M.op X0 X1) x)) (M.op X4 (M.op X0 X5))) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq5246 X0 X1 x X3 X4 X5
       have i₂ := eq5038 (M.op X0 X1) x
       grind)
    | exact superpose eq5038 eq5246
    | exact resolve eq5246 eq5038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5246
  have eq5556 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op x (M.op (M.op X0 X1) x))) = (M.op (M.op x (M.op X0 x)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5410 X0 X1 X2
       have i₂ := eq5039 X0 (M.op X0 X1)
       grind)
    | exact superpose eq5039 eq5410
    | exact resolve eq5410 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5410
  have eq5559 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op X4 X0) X4) X0) = (M.op (M.op x (M.op (M.op (M.op X0 X1) X2) x)) (M.op x (M.op (M.op X0 X1) x))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq5413 X0 X1 X2 x X4
       have i₂ := eq5038 (M.op (M.op X0 X1) X2) x
       grind)
    | exact superpose eq5038 eq5413
    | exact resolve eq5413 eq5038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5413
  have eq5560 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 (M.op X0 X4)) X0) = (M.op (M.op x (M.op (M.op (M.op X0 X1) X2) x)) (M.op x (M.op (M.op X0 X1) x))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq5414 X0 X1 X2 x X4
       have i₂ := eq5038 (M.op (M.op X0 X1) X2) x
       grind)
    | exact superpose eq5038 eq5414
    | exact resolve eq5414 eq5038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5038 eq5414
  have eq5584 : ∀ X0 X1 X4 X5 : G, (M.op (M.op x (M.op (M.op X0 X1) x)) (M.op X4 (M.op X0 X5))) = (M.op x (M.op X4 x)) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq5449 X0 X1 x X4 X5
       have i₂ := eq5039 x X4
       grind)
    | exact superpose eq5039 eq5449
    | exact resolve eq5449 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5449
  have eq5667 : ∀ X0 X1 X2 : G, (M.op (M.op x (M.op X0 x)) X0) = (M.op (M.op x (M.op (M.op (M.op X0 X1) X2) x)) (M.op x (M.op (M.op X0 X1) x))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5559 X0 X1 X2 x
       have i₂ := eq5039 x X0
       grind)
    | exact superpose eq5039 eq5559
    | exact resolve eq5559 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5559
  have eq5668 : ∀ X0 X1 X2 X4 : G, (M.op (M.op x (M.op (M.op (M.op X0 X1) X2) x)) (M.op x (M.op (M.op X0 X1) x))) = (M.op x (M.op (M.op X0 X4) x)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq5560 X0 X1 X2 X4
       have i₂ := eq5039 X0 (M.op X0 X4)
       grind)
    | exact superpose eq5039 eq5560
    | exact resolve eq5560 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5560
  have eq5723 : ∀ X0 : G, (M.op x (M.op x x)) = (M.op (M.op x (M.op X0 x)) X0) := by
    intro X0
    first
    | (have i₁ := eq5667 X0 x x
       have i₂ := eq5584 (M.op X0 x) x x x
       grind)
    | exact superpose eq5584 eq5667
    | exact resolve eq5667 eq5584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5667
  have eq5724 : ∀ X0 X4 : G, (M.op x (M.op x x)) = (M.op x (M.op (M.op X0 X4) x)) := by
    intro X0 X4
    first
    | (have i₁ := eq5668 X0 x x X4
       have i₂ := eq5584 (M.op X0 x) x x x
       grind)
    | exact superpose eq5584 eq5668
    | exact resolve eq5668 eq5584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5668
  have eq5760 : ∀ X0 : G, x = (M.op (M.op x (M.op X0 x)) X0) := by
    intro X0
    first
    | (have i₁ := eq5723 X0
       have i₂ := eq5042 x
       grind)
    | exact superpose eq5042 eq5723
    | exact resolve eq5723 eq5042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5723
  have eq5761 : ∀ X0 X4 : G, x = (M.op x (M.op (M.op X0 X4) x)) := by
    intro X0 X4
    first
    | (have i₁ := eq5724 X0 X4
       have i₂ := eq5042 x
       grind)
    | exact superpose eq5042 eq5724
    | exact resolve eq5724 eq5042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5724
  have eq5939 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X4 X1) X4)) = (M.op (M.op (M.op X2 (M.op (M.op X3 X1) X3)) X2) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq151 X2 (M.op (M.op X3 X1) X3) X1 X4
       have i₂ := eq17 X3 X1 X0
       grind)
    | exact superpose eq17 eq151
    | exact resolve eq151 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq5949 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X2) (M.op (M.op X5 (M.op X4 X2)) X5)) = (M.op (M.op (M.op X3 X4) X3) (M.op (M.op (M.op X0 X1) X0) (M.op X2 X1))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq151 X3 X4 (M.op X4 X2) X5
       have i₂ := eq54 X0 X1 X4 X2
       grind)
    | (have i₁ := eq151 X0 (M.op X3 X1) (M.op (M.op X0 X1) X0) X3
       have i₂ := eq54 X0 X1 X2 X3
       grind)
    | exact superpose eq54 eq151
    | exact resolve eq151 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq5968 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 (M.op X0 X3)) X2) (M.op X0 (M.op X0 X1))) = (M.op (M.op (M.op X4 X3) X4) (M.op (M.op X5 (M.op (M.op X4 X3) X4)) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq151 X2 (M.op X0 X3) (M.op (M.op X4 X3) X4) X5
       have i₂ := eq63 X4 X3 X0 X1
       grind)
    | (have i₁ := eq151 X0 (M.op X2 X3) X2 X3
       have i₂ := eq63 X0 X1 X2 X3
       grind)
    | exact superpose eq63 eq151
    | exact resolve eq151 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq6062 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X4) X3) (M.op X2 X4)) = (M.op X2 (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq151 X3 X4 X2 (M.op (M.op X1 X2) X1)
       have i₂ := eq64 X1 X2 (M.op (M.op X1 X2) X1) X0
       grind)
    | exact superpose eq64 eq151
    | exact resolve eq151 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq151
  have eq6320 : ∀ X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X4) X3) (M.op X2 X4)) = (M.op X2 (M.op x (M.op (M.op (M.op (M.op X1 X2) X1) X2) x))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq6062 x X1 X2 X3 X4
       have i₂ := eq5039 x (M.op (M.op (M.op X1 X2) X1) X2)
       grind)
    | exact superpose eq5039 eq6062
    | exact resolve eq6062 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6062
  have eq6368 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 (M.op X0 X3)) X2) (M.op X0 (M.op X0 X1))) = (M.op (M.op (M.op X4 X3) X4) (M.op x (M.op (M.op (M.op X4 X3) X4) x))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5968 X0 X1 X2 X3 X4 x
       have i₂ := eq5039 x (M.op (M.op X4 X3) X4)
       grind)
    | exact superpose eq5039 eq5968
    | exact resolve eq5968 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5968
  have eq6387 : ∀ X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X2) (M.op (M.op X5 (M.op X4 X2)) X5)) = (M.op (M.op (M.op X3 X4) X3) (M.op (M.op x (M.op X1 x)) (M.op X2 X1))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq5949 x X1 X2 X3 X4 X5
       have i₂ := eq5039 x X1
       grind)
    | exact superpose eq5039 eq5949
    | exact resolve eq5949 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5949
  have eq6393 : ∀ X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X4 X1) X4)) = (M.op (M.op (M.op X2 (M.op (M.op X3 X1) X3)) X2) (M.op x (M.op X1 x))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq5939 x X1 X2 X3 X4
       have i₂ := eq5039 x X1
       grind)
    | exact superpose eq5039 eq5939
    | exact resolve eq5939 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5939
  have eq6534 : ∀ X2 X3 X4 : G, (M.op (M.op (M.op X3 X4) X3) (M.op X2 X4)) = (M.op X2 x) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq6320 x X2 X3 X4
       have i₂ := eq5761 (M.op (M.op x X2) x) X2
       grind)
    | exact superpose eq5761 eq6320
    | exact resolve eq6320 eq5761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6320
  have eq6574 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 (M.op X0 X3)) X2) (M.op X0 (M.op X0 X1))) = (M.op (M.op x (M.op (M.op X4 X3) x)) (M.op X4 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6368 X0 X1 X2 X3 X4
       have i₂ := eq5556 (M.op X4 X3) X4 X4
       grind)
    | exact superpose eq5556 eq6368
    | exact resolve eq6368 eq5556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6368
  have eq6593 : ∀ X1 X2 X4 X5 : G, (M.op (M.op X4 X2) (M.op (M.op X5 (M.op X4 X2)) X5)) = (M.op (M.op x (M.op X4 x)) (M.op (M.op x (M.op X1 x)) (M.op X2 X1))) := by
    intro X1 X2 X4 X5
    first
    | (have i₁ := eq6387 X1 X2 x X4 X5
       have i₂ := eq5039 x X4
       grind)
    | exact superpose eq5039 eq6387
    | exact resolve eq6387 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6387
  have eq6599 : ∀ X1 X3 X4 : G, (M.op X1 (M.op (M.op X4 X1) X4)) = (M.op (M.op x (M.op (M.op (M.op X3 X1) X3) x)) (M.op x (M.op X1 x))) := by
    intro X1 X3 X4
    first
    | (have i₁ := eq6393 X1 x X3 X4
       have i₂ := eq5039 x (M.op (M.op X3 X1) X3)
       grind)
    | exact superpose eq5039 eq6393
    | exact resolve eq6393 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6393
  have eq6714 : ∀ X2 X4 : G, (M.op X2 x) = (M.op (M.op x (M.op X4 x)) (M.op X2 X4)) := by
    intro X2 X4
    first
    | (have i₁ := eq6534 X2 x X4
       have i₂ := eq5039 x X4
       grind)
    | exact superpose eq5039 eq6534
    | exact resolve eq6534 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6534
  have eq6741 : ∀ X0 X1 X2 X3 : G, x = (M.op (M.op (M.op X2 (M.op X0 X3)) X2) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6574 X0 X1 X2 X3 x
       have i₂ := eq5760 (M.op x X3)
       grind)
    | exact superpose eq5760 eq6574
    | exact resolve eq6574 eq5760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5760 eq6574
  have eq6760 : ∀ X1 X2 X4 : G, (M.op (M.op X4 X2) (M.op x (M.op (M.op X4 X2) x))) = (M.op (M.op x (M.op X4 x)) (M.op (M.op x (M.op X1 x)) (M.op X2 X1))) := by
    intro X1 X2 X4
    first
    | (have i₁ := eq6593 X1 X2 X4 x
       have i₂ := eq5039 x (M.op X4 X2)
       grind)
    | exact superpose eq5039 eq6593
    | exact resolve eq6593 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6593
  have eq6766 : ∀ X1 X4 : G, (M.op X1 (M.op (M.op X4 X1) X4)) = (M.op x (M.op x (M.op X1 x))) := by
    intro X1 X4
    first
    | (have i₁ := eq6599 X1 x X4
       have i₂ := eq5761 (M.op x X1) x
       grind)
    | exact superpose eq5761 eq6599
    | exact resolve eq6599 eq5761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5761 eq6599
  have eq6882 : ∀ X0 X1 X3 : G, x = (M.op (M.op x (M.op (M.op X0 X3) x)) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq6741 X0 X1 x X3
       have i₂ := eq5039 x (M.op X0 X3)
       grind)
    | exact superpose eq5039 eq6741
    | exact resolve eq6741 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6741
  have eq6898 : ∀ X2 X4 : G, (M.op (M.op X4 X2) (M.op x (M.op (M.op X4 X2) x))) = (M.op (M.op x (M.op X4 x)) (M.op X2 x)) := by
    intro X2 X4
    first
    | (have i₁ := eq6760 x X2 X4
       have i₂ := eq6714 X2 x
       grind)
    | exact superpose eq6714 eq6760
    | exact resolve eq6760 eq6714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6714 eq6760
  have eq6904 : ∀ X1 X4 : G, x = (M.op X1 (M.op (M.op X4 X1) X4)) := by
    intro X1 X4
    first
    | (have i₁ := eq6766 X1 X4
       have i₂ := eq5042 (M.op X1 x)
       grind)
    | exact superpose eq5042 eq6766
    | exact resolve eq6766 eq5042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5042 eq6766
  have eq6982 : ∀ X0 : G, x = (M.op x (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq6882 X0 x x
       have i₂ := eq5584 X0 x X0 x
       grind)
    | exact superpose eq5584 eq6882
    | exact resolve eq6882 eq5584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5584 eq6882
  have eq6996 : ∀ X2 X4 : G, (M.op (M.op x (M.op X4 x)) X4) = (M.op (M.op x (M.op X4 x)) (M.op X2 x)) := by
    intro X2 X4
    first
    | (have i₁ := eq6898 X2 X4
       have i₂ := eq5556 X4 X2 X2
       grind)
    | exact superpose eq5556 eq6898
    | exact resolve eq6898 eq5556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5556 eq6898
  have eq6998 : ∀ X1 : G, x = (M.op X1 (M.op x (M.op X1 x))) := by
    intro X1
    first
    | (have i₁ := eq6904 X1 x
       have i₂ := eq5039 x X1
       grind)
    | exact superpose eq5039 eq6904
    | exact resolve eq6904 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5039 eq6904
  have eq7038 : ∀ X2 X4 : G, (M.op x (M.op X2 x)) = (M.op x X4) := by
    intro X2 X4
    first
    | (have i₁ := eq6996 X2 x
       have i₂ := eq6982 x
       grind)
    | exact superpose eq6982 eq6996
    | exact resolve eq6996 eq6982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6996
  have eq7040 : ∀ X1 : G, x = (M.op X1 x) := by
    intro X1
    first
    | (have i₁ := eq6998 X1
       have i₂ := eq6982 X1
       grind)
    | exact superpose eq6982 eq6998
    | exact resolve eq6998 eq6982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6998
  have eq7061 : ∀ X4 : G, x = (M.op x X4) := by
    intro X4
    first
    | (have i₁ := eq7038 x X4
       have i₂ := eq6982 x
       grind)
    | exact superpose eq6982 eq7038
    | exact resolve eq7038 eq6982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6982 eq7038
  have eq7132 : ∀ X0 X1 : G, x = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1 x
       have i₂ := eq7040 (M.op x X1)
       grind)
    | exact superpose eq7040 eq19
    | exact resolve eq19 eq7040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq7040
  have eq29968 : x = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq7132 (σ x) (σ x)
       have i₂ := eq4449
       grind)
    | exact superpose eq4449 eq7132
    | exact resolve eq7132 eq4449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7132
  have eq30917 : x = (σ x) := by
    first
    | (have i₁ := eq4449
       have i₂ := eq29968
       grind)
    | exact superpose eq29968 eq4449
    | exact resolve eq4449 eq29968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4449 eq29968
  have eq32703 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq30917
       grind)
    | exact superpose eq30917 eq14
    | exact resolve eq14 eq30917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32747 : x ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq32703
       have i₂ := eq7061 (σ y)
       grind)
    | exact superpose eq7061 eq32703
    | exact resolve eq32703 eq7061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32703
  have eq32758 : x ≠ (σ x) := by
    first
    | (have i₁ := eq32747
       have i₂ := eq7061 y
       grind)
    | exact superpose eq7061 eq32747
    | exact resolve eq32747 eq7061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7061 eq32747
  have eq32761 : False := by grind
  exact eq32761

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation442 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law442 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
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
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq84 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq88 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq84 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq84 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq84 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq104 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq88 (σ X0) (σ X1)
       grind)
    | exact superpose eq88 eq13
    | exact resolve eq13 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0 X1
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq104
    | exact resolve eq104 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq104
  have eq1063 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq109 x y
       grind)
    | exact superpose eq109 eq14
    | (have r₁ := eq14
       have r₂ := eq109 x y
       grind)
    | exact resolve eq14 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq1088 : False := by grind
  exact eq1088

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation442 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law442 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X0)))) = X0 := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 (M.op X2 X0))) = (M.op (M.op X1 (M.op X1 (M.op X2 X0))) (M.op X3 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X1 (M.op X1 (M.op X2 X0))) X3 X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X0) X0 X0
       have i₂ := eq8 X0 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq29 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 X0))) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
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
  have eq31 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq37 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq40 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq48 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq37
    | exact resolve eq37 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq27
    | exact resolve eq27 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq27 (τ X0) X1
       grind)
    | exact superpose eq27 eq17
    | (have j1 := eq27 (τ X0) X1
       grind)
    | exact resolve eq17 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq99 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq101 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq45 X1 X0
       have i₂ := eq12 (σ X1) X0
       grind)
    | exact superpose eq12 eq45
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq113 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq99 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq99
    | exact resolve eq99 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq126 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 X2) (M.op X0 X0)) ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X1 X2) X0 X1
       have i₂ := eq29 X2 X0 X1
       grind)
    | exact superpose eq29 eq8
    | (have j1 := eq29 X2 X0 X2
       grind)
    | exact resolve eq8 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq137 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (M.op X0 X1)
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq63
    | (have j0 := eq63 X1 X0
       grind)
    | exact resolve eq63 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq207 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X1) (σ X0)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq20
    | (have j1 := eq31 X1 X0
       grind)
    | exact resolve eq20 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X1) (σ X1)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq20
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq20 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq203 X0
       have i₂ := eq13 X0 (k X0 X0)
       grind)
    | exact superpose eq13 eq203
    | (have j0 := eq203 X0
       grind)
    | exact resolve eq203 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq244 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq113 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq113
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq113 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq263 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq244 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq244
    | (have j0 := eq244 X0 X1
       grind)
    | exact resolve eq244 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq338 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X3 X2)) = (M.op (M.op X3 (M.op X3 X2)) (M.op X4 (M.op X4 (M.op X0 (M.op X0 (M.op X1 X2)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op X3 (M.op X3 X2)) X4 (M.op X0 (M.op X0 (M.op X1 X2)))
       have i₂ := eq18 X2 X0 X1 X3
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq681 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq40 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq40
    | exact resolve eq40 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq765 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq681 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq681
    | (have j0 := eq681 X0 X1
       grind)
    | exact resolve eq681 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq790 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq60 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq60
    | exact resolve eq60 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq837 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq790 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq790
    | (have j0 := eq790 X0 X1
       grind)
    | exact resolve eq790 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq1116 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X0) (σ X1)
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq20
    | (have j1 := eq57 X0 X1
       grind)
    | exact resolve eq20 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq1454 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq16 X0 (k (τ X0) (τ X0))
       have i₂ := eq233 (τ X0)
       grind)
    | exact superpose eq233 eq16
    | (have j1 := eq233 (τ X0)
       grind)
    | exact resolve eq16 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq233
  have eq1492 : ∀ X0 : G, (σ (τ X0)) = (k X0 (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1454 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1454
    | (have j0 := eq1454 X0
       grind)
    | exact resolve eq1454 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1454
  have eq1498 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1492 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1492
    | (have j0 := eq1492 X0
       grind)
    | exact resolve eq1492 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1492
  have eq1501 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1498 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1498
    | (have j0 := eq1498 X0
       grind)
    | exact resolve eq1498 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498
  have eq1876 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq126
  have eq2154 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq224 x y
       grind)
    | exact superpose eq224 eq14
    | (have j1 := eq224 x y
       grind)
    | exact resolve eq14 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2181 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq224 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq2951 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq207 (τ X1) (τ X0)
       have i₂ := eq48 X0 X1
       grind)
    | exact superpose eq48 eq207
    | (have j0 := eq207 (τ X0) (τ X1)
       grind)
    | exact resolve eq207 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq3011 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2951 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2951
    | (have j0 := eq2951 X0 X1
       grind)
    | exact resolve eq2951 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2951
  have eq3016 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3011 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq3011
    | (have j0 := eq3011 X0 X1
       grind)
    | exact resolve eq3011 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3011
  have eq3017 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (k X0 X1) = (M.op (k X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3016 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3016
    | (have j0 := eq3016 X0 X1
       grind)
    | exact resolve eq3016 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3016
  have eq3018 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3017 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3017
    | (have j0 := eq3017 X0 X1
       grind)
    | exact resolve eq3017 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3017
  have eq5315 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2181 (τ X1) (τ X0)
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq2181
    | (have j0 := eq2181 (τ X1) (τ X0)
       grind)
    | exact resolve eq2181 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq5339 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5315 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq5315
    | (have j0 := eq5315 X0 X1
       grind)
    | exact resolve eq5315 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5315
  have eq5347 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5339 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5339
    | (have j0 := eq5339 X0 X1
       grind)
    | exact resolve eq5339 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5339
  have eq5350 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5347 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5347
    | (have j0 := eq5347 X0 X1
       grind)
    | exact resolve eq5347 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5347
  have eq5351 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5350 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5350
    | (have j0 := eq5350 X0 X1
       grind)
    | exact resolve eq5350 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5350
  have eq7622 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op (M.op X2 (M.op X2 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq338 (M.op X0 X1) X0 X1 X2 (M.op X0 X1)
       have i₂ := eq8 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq8 eq338
    | exact resolve eq338 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq7717 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7622 X0 (M.op X1 (M.op X2 X1)) X1
       have i₂ := eq8 X1 X1 X2
       grind)
    | exact superpose eq8 eq7622
    | exact resolve eq7622 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7622
  have eq8443 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq263 x y
       grind)
    | exact superpose eq263 eq14
    | (have j1 := eq263 x y
       grind)
    | exact resolve eq14 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8503 : y = (k y x) := by
    first
    | (have j1 := eq837 x y
       grind)
    | (have r₁ := eq8443
       have r₂ := eq837 x y
       grind)
    | exact resolve eq8443 eq837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837 eq8443
  have eq9121 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq765 x y
       have i₂ := eq8503
       grind)
    | exact superpose eq8503 eq765
    | (have j0 := eq765 x y
       grind)
    | exact resolve eq765 eq8503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9123 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2181 x y
       have i₂ := eq8503
       grind)
    | exact superpose eq8503 eq2181
    | (have j0 := eq2181 x y
       grind)
    | exact resolve eq2181 eq8503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9124 : y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3018 y x
       have i₂ := eq8503
       grind)
    | exact superpose eq8503 eq3018
    | (have j0 := eq3018 y y
       grind)
    | exact resolve eq3018 eq8503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11361 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq137 y y
       have i₂ := eq9124
       grind)
    | exact superpose eq9124 eq137
    | (have r₁ := eq137 y y
       have r₂ := eq9124
       grind)
    | exact resolve eq137 eq9124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq11374 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq9124
  have eq11375 : y = (k y y) ∨ x = (M.op y y) := by grind
  clear eq11361
  have eq12388 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2181 y y
       have i₂ := eq11375
       grind)
    | exact superpose eq11375 eq2181
    | (have j0 := eq2181 y y
       grind)
    | exact resolve eq2181 eq11375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2181 eq11375
  have eq12393 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq12388
  have eq44527 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2154
       have i₂ := eq765 x y
       grind)
    | exact superpose eq765 eq2154
    | (have j1 := eq765 x y
       grind)
    | (have r₁ := eq2154
       have r₂ := eq765 x y
       grind)
    | exact resolve eq2154 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765 eq2154
  have eq44535 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq44527
  have eq44552 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq44535
       grind)
    | exact superpose eq44535 eq14
    | exact resolve eq14 eq44535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44566 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq101 (σ x) y
       have i₂ := eq44535
       grind)
    | exact superpose eq44535 eq101
    | (have j0 := eq101 (σ x) y
       grind)
    | exact resolve eq101 eq44535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq44535
  have eq44676 : x = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq44566
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq44566
    | exact resolve eq44566 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44566
  have eq44694 : x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq44676
       have i₂ := eq8503
       grind)
    | exact superpose eq8503 eq44676
    | exact resolve eq44676 eq8503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8503 eq44676
  have eq44698 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq44694
       have r₂ := eq11374
       grind)
    | exact resolve eq44694 eq11374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11374 eq44694
  have eq44997 : (σ x) ≠ (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq44552
       have i₂ := eq9121
       grind)
    | exact superpose eq9121 eq44552
    | exact resolve eq44552 eq9121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9121 eq44552
  have eq44999 : (σ x) ≠ (σ y) ∨ x = (M.op y y) := by grind
  clear eq44997
  have eq46579 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12393
       have i₂ := eq44698
       grind)
    | exact superpose eq44698 eq12393
    | exact resolve eq12393 eq44698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12393 eq44698
  have eq46742 : (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq46579
  have eq46777 : x = (M.op y y) := by
    first
    | (have r₁ := eq46742
       have r₂ := eq44999
       grind)
    | exact resolve eq46742 eq44999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44999 eq46742
  have eq47553 : x = (k y y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq1876 y
       have i₂ := eq46777
       grind)
    | exact superpose eq46777 eq1876
    | exact resolve eq1876 eq46777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1876
  have eq47560 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq8 y X0 y
       have i₂ := eq46777
       grind)
    | exact superpose eq46777 eq8
    | exact resolve eq8 eq46777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47564 : x = (M.op x y) := by
    first
    | (have i₁ := eq20 y y
       have i₂ := eq46777
       grind)
    | exact superpose eq46777 eq20
    | exact resolve eq20 eq46777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq47568 : x ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq63 y y
       have i₂ := eq46777
       grind)
    | exact superpose eq46777 eq63
    | (have j0 := eq63 y y
       grind)
    | exact resolve eq63 eq46777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq47650 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op y x))) := by
    intro X0
    first
    | (have i₁ := eq7717 y y X0
       have i₂ := eq46777
       grind)
    | exact superpose eq46777 eq7717
    | exact resolve eq7717 eq46777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7717
  have eq51224 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq1116 y y
       have i₂ := eq47553
       grind)
    | exact superpose eq47553 eq1116
    | exact resolve eq1116 eq47553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47553
  have eq51236 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | (have r₁ := eq51224
       have r₂ := eq9123
       grind)
    | exact resolve eq51224 eq9123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51224
  have eq63169 : (σ (M.op x y)) ≠ (σ x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq51236
       grind)
    | exact superpose eq51236 eq14
    | exact resolve eq14 eq51236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51236
  have eq63306 : (σ x) ≠ (σ x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq63169
       have i₂ := eq47564
       grind)
    | exact superpose eq47564 eq63169
    | exact resolve eq63169 eq47564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63169
  have eq63307 : x = (k x x) := by grind
  clear eq63306
  have eq64062 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5351 x x
       have i₂ := eq63307
       grind)
    | exact superpose eq63307 eq5351
    | (have j0 := eq5351 x x
       grind)
    | (have r₁ := eq5351 x x
       have r₂ := eq63307
       grind)
    | exact resolve eq5351 eq63307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5351 eq63307
  have eq64067 : x = (M.op x x) := by grind
  clear eq64062
  have eq64743 : y = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq47560 x
       have i₂ := eq64067
       grind)
    | exact superpose eq64067 eq47560
    | exact resolve eq47560 eq64067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47560
  have eq64910 : y = (M.op y x) := by
    first
    | (have i₁ := eq64743
       have i₂ := eq64067
       grind)
    | exact superpose eq64067 eq64743
    | exact resolve eq64743 eq64067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64067 eq64743
  have eq65328 : ∀ X0 : G, y = (M.op y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq47650 X0
       have i₂ := eq64910
       grind)
    | exact superpose eq64910 eq47650
    | exact resolve eq47650 eq64910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47650 eq64910
  have eq68197 : ∀ X0 : G, y = (M.op y (k y X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq65328 (k y X0)
       have i₂ := eq3018 y X0
       grind)
    | exact superpose eq3018 eq65328
    | (have j1 := eq3018 y X0
       grind)
    | exact resolve eq65328 eq3018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3018 eq65328
  have eq68424 : ∀ X0 : G, y = (M.op y (k y X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq68197 X0
       have i₂ := eq46777
       grind)
    | exact superpose eq46777 eq68197
    | (have j0 := eq68197 X0
       grind)
    | exact resolve eq68197 eq46777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68197
  have eq81832 : y = (M.op y y) ∨ x = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq68424 (τ (M.op (σ y) (σ y)))
       have i₂ := eq113 y
       grind)
    | exact superpose eq113 eq68424
    | (have j0 := eq68424 (τ (M.op (σ y) (σ y)))
       grind)
    | exact resolve eq68424 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq81839 : y = (M.op y y) ∨ x = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq68424 (k y y)
       have i₂ := eq1501 y
       grind)
    | exact superpose eq1501 eq68424
    | (have j0 := eq68424 (k y y)
       have j1 := eq1501 y
       grind)
    | exact resolve eq68424 eq1501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1501 eq68424
  have eq81937 : y = (M.op y y) ∨ x = (k y y) := by grind
  clear eq81839
  have eq81969 : x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq81937
       have i₂ := eq46777
       grind)
    | exact superpose eq46777 eq81937
    | exact resolve eq81937 eq46777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81937
  have eq81976 : x = (τ (M.op (σ y) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq81832
       have i₂ := eq46777
       grind)
    | exact superpose eq46777 eq81832
    | exact resolve eq81832 eq46777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46777 eq81832
  have eq92316 : x = (τ (σ (k y y))) ∨ x = y ∨ y = (k y y) := by
    first
    | (have i₁ := eq81976
       have i₂ := eq263 y y
       grind)
    | exact superpose eq263 eq81976
    | (have j1 := eq263 y y
       grind)
    | exact resolve eq81976 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263 eq81976
  have eq92480 : x = (τ (σ (k y y))) ∨ y = (k y y) := by
    first
    | (have r₁ := eq92316
       have r₂ := eq47568
       grind)
    | exact resolve eq92316 eq47568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47568 eq92316
  have eq92492 : y = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq92480
       have i₂ := eq9 (k y y)
       grind)
    | exact superpose eq9 eq92480
    | exact resolve eq92480 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92480
  have eq92895 : x ≠ y ∨ x = (k y y) := by grind
  clear eq92492
  have eq92918 : x = (k y y) := by
    first
    | (have r₁ := eq92895
       have r₂ := eq81969
       grind)
    | exact resolve eq92895 eq81969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81969 eq92895
  have eq93363 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1116 y y
       have i₂ := eq92918
       grind)
    | exact superpose eq92918 eq1116
    | exact resolve eq1116 eq92918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116 eq92918
  have eq93379 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq93363
       have r₂ := eq9123
       grind)
    | exact resolve eq93363 eq9123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9123 eq93363
  have eq93845 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq93379
       grind)
    | exact superpose eq93379 eq14
    | exact resolve eq14 eq93379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93379
  have eq93938 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq93845
       have i₂ := eq47564
       grind)
    | exact superpose eq47564 eq93845
    | exact resolve eq93845 eq47564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47564 eq93845
  have eq93939 : False := by grind
  exact eq93939

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pxy_Equation442 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law442 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X0)))) = X0 := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 (M.op X2 X0))) = (M.op (M.op X1 (M.op X1 (M.op X2 X0))) (M.op X3 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X1 (M.op X1 (M.op X2 X0))) X3 X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X0) X0 X0
       have i₂ := eq8 X0 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq29 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 X0))) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq31 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq33 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq48 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq51 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq53 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq36
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq58 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq51 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq51
    | exact resolve eq51 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq27
    | exact resolve eq27 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq27 (τ X0) X1
       grind)
    | exact superpose eq27 eq16
    | (have j1 := eq27 (τ X0) X1
       grind)
    | exact resolve eq16 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq65 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq126 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 X2) (M.op X0 X0)) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X1 X2) X0 X1
       have i₂ := eq29 X2 X0 X1
       grind)
    | exact superpose eq29 eq8
    | (have j1 := eq29 X2 X0 X2
       grind)
    | exact resolve eq8 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq137 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 (M.op X0 X1) X1
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq65
    | (have j0 := eq65 X0 X1
       grind)
    | exact resolve eq65 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 : G, (σ X0) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq207 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X1) (σ X0)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq20
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq20 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X1) (σ X1)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq20
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq20 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 : G, (σ X0) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq203 X0
       have i₂ := eq13 (k X0 X0) X0
       grind)
    | exact superpose eq13 eq203
    | (have j0 := eq203 X0
       grind)
    | exact resolve eq203 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq244 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq58
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq58 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq263 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq244 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq244
    | (have j0 := eq244 X0 X1
       grind)
    | exact resolve eq244 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq338 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X3 X2)) = (M.op (M.op X3 (M.op X3 X2)) (M.op X4 (M.op X4 (M.op X0 (M.op X0 (M.op X1 X2)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op X3 (M.op X3 X2)) X4 (M.op X0 (M.op X0 (M.op X1 X2)))
       have i₂ := eq18 X2 X0 X1 X3
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq681 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq33
    | exact resolve eq33 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq765 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq681 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq681
    | (have j0 := eq681 X0 X1
       grind)
    | exact resolve eq681 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq790 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
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
  clear eq64
  have eq837 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq790 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq790
    | (have j0 := eq790 X0 X1
       grind)
    | exact resolve eq790 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq1116 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X1) (σ X0)
       have i₂ := eq59 X0 X1
       grind)
    | exact superpose eq59 eq20
    | (have j1 := eq59 X0 X1
       grind)
    | exact resolve eq20 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq1454 : ∀ X0 : G, (σ (τ X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (k (τ X0) (τ X0))
       have i₂ := eq233 (τ X0)
       grind)
    | exact superpose eq233 eq17
    | (have j1 := eq233 (τ X0)
       grind)
    | exact resolve eq17 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq1492 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1454 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1454
    | (have j0 := eq1454 X0
       grind)
    | exact resolve eq1454 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1454
  have eq1498 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1492 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1492
    | (have j0 := eq1492 X0
       grind)
    | exact resolve eq1492 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1492
  have eq1501 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1498 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1498
    | (have j0 := eq1498 X0
       grind)
    | exact resolve eq1498 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498
  have eq1879 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq126
  have eq2200 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq224 x y
       grind)
    | exact superpose eq224 eq14
    | (have j1 := eq224 x y
       grind)
    | exact resolve eq14 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2227 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq224 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq3108 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq207 (τ X1) (τ X0)
       have i₂ := eq48 X0 X1
       grind)
    | exact superpose eq48 eq207
    | (have j0 := eq207 (τ X0) (τ X1)
       grind)
    | exact resolve eq207 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq3174 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3108 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3108
    | (have j0 := eq3108 X0 X1
       grind)
    | exact resolve eq3108 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3108
  have eq3176 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3174 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq3174
    | (have j0 := eq3174 X0 X1
       grind)
    | exact resolve eq3174 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3174
  have eq3177 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (k X0 X1) = (M.op (k X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3176 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3176
    | (have j0 := eq3176 X0 X1
       grind)
    | exact resolve eq3176 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3176
  have eq3178 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3177 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3177
    | (have j0 := eq3177 X0 X1
       grind)
    | exact resolve eq3177 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3177
  have eq4918 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2227 (τ X0) (τ X1)
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq2227
    | (have j0 := eq2227 (τ X0) (τ X1)
       grind)
    | exact resolve eq2227 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq4951 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4918 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq4918
    | (have j0 := eq4918 X0 X1
       grind)
    | exact resolve eq4918 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4918
  have eq4956 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4951 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4951
    | (have j0 := eq4951 X0 X1
       grind)
    | exact resolve eq4951 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4951
  have eq4957 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4956 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4956
    | (have j0 := eq4956 X0 X1
       grind)
    | exact resolve eq4956 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4956
  have eq4958 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4957 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4957
    | (have j0 := eq4957 X0 X1
       grind)
    | exact resolve eq4957 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4957
  have eq7200 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq263 x y
       grind)
    | exact superpose eq263 eq14
    | (have j1 := eq263 x y
       grind)
    | exact resolve eq14 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7246 : y = (k x y) := by
    first
    | (have j1 := eq837 x y
       grind)
    | (have r₁ := eq7200
       have r₂ := eq837 x y
       grind)
    | exact resolve eq7200 eq837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837 eq7200
  have eq7425 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq765 x y
       have i₂ := eq7246
       grind)
    | exact superpose eq7246 eq765
    | (have j0 := eq765 x y
       grind)
    | exact resolve eq765 eq7246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7427 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2227 x y
       have i₂ := eq7246
       grind)
    | exact superpose eq7246 eq2227
    | (have j0 := eq2227 x y
       grind)
    | exact resolve eq2227 eq7246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7428 : y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3178 x y
       have i₂ := eq7246
       grind)
    | exact superpose eq7246 eq3178
    | (have j0 := eq3178 y y
       grind)
    | exact resolve eq3178 eq7246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7573 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op (M.op X2 (M.op X2 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq338 (M.op X0 X1) X0 X1 X2 (M.op X0 X1)
       have i₂ := eq8 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq8 eq338
    | exact resolve eq338 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq8763 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq137 y y
       have i₂ := eq7428
       grind)
    | exact superpose eq7428 eq137
    | (have r₁ := eq137 y y
       have r₂ := eq7428
       grind)
    | exact resolve eq137 eq7428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq8771 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq7428
  have eq8772 : y = (k y y) ∨ x = (M.op y y) := by grind
  clear eq8763
  have eq10937 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2227 y y
       have i₂ := eq8772
       grind)
    | exact superpose eq8772 eq2227
    | (have j0 := eq2227 y y
       grind)
    | exact resolve eq2227 eq8772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2227 eq8772
  have eq10942 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq10937
  have eq17995 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7573 X0 (M.op X1 (M.op X2 X1)) X1
       have i₂ := eq8 X1 X1 X2
       grind)
    | exact superpose eq8 eq7573
    | exact resolve eq7573 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7573
  have eq44633 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2200
       have i₂ := eq765 x y
       grind)
    | exact superpose eq765 eq2200
    | (have j1 := eq765 x y
       grind)
    | (have r₁ := eq2200
       have r₂ := eq765 x y
       grind)
    | exact resolve eq2200 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765 eq2200
  have eq44641 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq44633
  have eq44660 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq44641
       grind)
    | exact superpose eq44641 eq14
    | exact resolve eq14 eq44641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44672 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq53 (σ x) y
       have i₂ := eq44641
       grind)
    | exact superpose eq44641 eq53
    | (have j0 := eq53 (σ x) y
       grind)
    | exact resolve eq53 eq44641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq44641
  have eq44784 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq44672
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq44672
    | exact resolve eq44672 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44672
  have eq44802 : x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq44784
       have i₂ := eq7246
       grind)
    | exact superpose eq7246 eq44784
    | exact resolve eq44784 eq7246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7246 eq44784
  have eq44806 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq44802
       have r₂ := eq8771
       grind)
    | exact resolve eq44802 eq8771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8771 eq44802
  have eq45100 : (σ x) ≠ (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq44660
       have i₂ := eq7425
       grind)
    | exact superpose eq7425 eq44660
    | exact resolve eq44660 eq7425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7425 eq44660
  have eq45102 : (σ x) ≠ (σ y) ∨ x = (M.op y y) := by grind
  clear eq45100
  have eq46684 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10942
       have i₂ := eq44806
       grind)
    | exact superpose eq44806 eq10942
    | exact resolve eq10942 eq44806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10942 eq44806
  have eq46845 : (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq46684
  have eq46878 : x = (M.op y y) := by
    first
    | (have r₁ := eq46845
       have r₂ := eq45102
       grind)
    | exact resolve eq46845 eq45102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45102 eq46845
  have eq47654 : x = (k y y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq1879 y
       have i₂ := eq46878
       grind)
    | exact superpose eq46878 eq1879
    | exact resolve eq1879 eq46878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879
  have eq47659 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq8 y X0 y
       have i₂ := eq46878
       grind)
    | exact superpose eq46878 eq8
    | exact resolve eq8 eq46878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47663 : x = (M.op x y) := by
    first
    | (have i₁ := eq20 y y
       have i₂ := eq46878
       grind)
    | exact superpose eq46878 eq20
    | exact resolve eq20 eq46878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq47667 : x ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq65 y y
       have i₂ := eq46878
       grind)
    | exact superpose eq46878 eq65
    | (have j0 := eq65 y y
       grind)
    | exact resolve eq65 eq46878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq47749 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op y x))) := by
    intro X0
    first
    | (have i₁ := eq17995 y y X0
       have i₂ := eq46878
       grind)
    | exact superpose eq46878 eq17995
    | exact resolve eq17995 eq46878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17995
  have eq51461 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq1116 y y
       have i₂ := eq47654
       grind)
    | exact superpose eq47654 eq1116
    | exact resolve eq1116 eq47654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47654
  have eq51473 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | (have r₁ := eq51461
       have r₂ := eq7427
       grind)
    | exact resolve eq51461 eq7427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51461
  have eq62892 : (σ (M.op x y)) ≠ (σ x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq51473
       grind)
    | exact superpose eq51473 eq14
    | exact resolve eq14 eq51473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51473
  have eq63030 : (σ x) ≠ (σ x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq62892
       have i₂ := eq47663
       grind)
    | exact superpose eq47663 eq62892
    | exact resolve eq62892 eq47663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62892
  have eq63031 : x = (k x x) := by grind
  clear eq63030
  have eq63262 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4958 x x
       have i₂ := eq63031
       grind)
    | exact superpose eq63031 eq4958
    | (have j0 := eq4958 x x
       grind)
    | (have r₁ := eq4958 x x
       have r₂ := eq63031
       grind)
    | exact resolve eq4958 eq63031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4958 eq63031
  have eq63267 : x = (M.op x x) := by grind
  clear eq63262
  have eq63649 : y = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq47659 x
       have i₂ := eq63267
       grind)
    | exact superpose eq63267 eq47659
    | exact resolve eq47659 eq63267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47659
  have eq63813 : y = (M.op y x) := by
    first
    | (have i₁ := eq63649
       have i₂ := eq63267
       grind)
    | exact superpose eq63267 eq63649
    | exact resolve eq63649 eq63267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63267 eq63649
  have eq64372 : ∀ X0 : G, y = (M.op y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq47749 X0
       have i₂ := eq63813
       grind)
    | exact superpose eq63813 eq47749
    | exact resolve eq47749 eq63813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47749 eq63813
  have eq66862 : ∀ X0 : G, y = (M.op y (k X0 y)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq64372 (k X0 y)
       have i₂ := eq3178 X0 y
       grind)
    | exact superpose eq3178 eq64372
    | (have j1 := eq3178 X0 y
       grind)
    | exact resolve eq64372 eq3178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3178 eq64372
  have eq67092 : ∀ X0 : G, y = (M.op y (k X0 y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq66862 X0
       have i₂ := eq46878
       grind)
    | exact superpose eq46878 eq66862
    | (have j0 := eq66862 X0
       grind)
    | exact resolve eq66862 eq46878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66862
  have eq78855 : y = (M.op y y) ∨ x = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq67092 (τ (M.op (σ y) (σ y)))
       have i₂ := eq58 y
       grind)
    | exact superpose eq58 eq67092
    | (have j0 := eq67092 (τ (M.op (σ y) (σ y)))
       grind)
    | exact resolve eq67092 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq78863 : y = (M.op y y) ∨ x = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq67092 (k y y)
       have i₂ := eq1501 y
       grind)
    | exact superpose eq1501 eq67092
    | (have j0 := eq67092 (k y y)
       have j1 := eq1501 y
       grind)
    | exact resolve eq67092 eq1501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1501 eq67092
  have eq78967 : y = (M.op y y) ∨ x = (k y y) := by grind
  clear eq78863
  have eq79000 : x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq78967
       have i₂ := eq46878
       grind)
    | exact superpose eq46878 eq78967
    | exact resolve eq78967 eq46878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78967
  have eq79008 : x = (τ (M.op (σ y) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq78855
       have i₂ := eq46878
       grind)
    | exact superpose eq46878 eq78855
    | exact resolve eq78855 eq46878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46878 eq78855
  have eq92003 : x = (τ (σ (k y y))) ∨ x = y ∨ y = (k y y) := by
    first
    | (have i₁ := eq79008
       have i₂ := eq263 y y
       grind)
    | exact superpose eq263 eq79008
    | (have j1 := eq263 y y
       grind)
    | exact resolve eq79008 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263 eq79008
  have eq92166 : x = (τ (σ (k y y))) ∨ y = (k y y) := by
    first
    | (have r₁ := eq92003
       have r₂ := eq47667
       grind)
    | exact resolve eq92003 eq47667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47667 eq92003
  have eq92177 : y = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq92166
       have i₂ := eq9 (k y y)
       grind)
    | exact superpose eq9 eq92166
    | exact resolve eq92166 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92166
  have eq92881 : x ≠ y ∨ x = (k y y) := by grind
  clear eq92177
  have eq92904 : x = (k y y) := by
    first
    | (have r₁ := eq92881
       have r₂ := eq79000
       grind)
    | exact resolve eq92881 eq79000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79000 eq92881
  have eq93048 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1116 y y
       have i₂ := eq92904
       grind)
    | exact superpose eq92904 eq1116
    | exact resolve eq1116 eq92904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116 eq92904
  have eq93064 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq93048
       have r₂ := eq7427
       grind)
    | exact resolve eq93048 eq7427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7427 eq93048
  have eq93663 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq93064
       grind)
    | exact superpose eq93064 eq14
    | exact resolve eq14 eq93064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93064
  have eq93855 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq93663
       have i₂ := eq47663
       grind)
    | exact superpose eq47663 eq93663
    | exact resolve eq93663 eq47663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47663 eq93663
  have eq93856 : False := by grind
  exact eq93856

/-- `Equation4423`: `x ◇ (x ◇ y) = (z ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pyx_Equation4423 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4423 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4423.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X0) := by
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
  have eq17 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) X1) = (M.op X1 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 (M.op X1 x) X3
       have i₂ := eq8 X1 x X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 x X3
       have i₂ := eq8 X1 x X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X0 X2 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq26 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X2)) ∨ (k X3 X0) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 X0
       have i₂ := eq12 X3 X0
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
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
  have eq28 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) X0) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X0 X1
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq31 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq27 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq67 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X2 X2)) = (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X2 X2) X1 X3
       have i₂ := eq19 X2 X1 X0
       grind)
    | (have i₁ := eq8 (M.op X2 X2) X1 X3
       have i₂ := eq19 X0 X1 X2
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24
    | exact resolve eq24 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) = (M.op (M.op X2 X2) (M.op (M.op X2 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 (M.op X2 X2) X3 X1
       have i₂ := eq19 X2 X1 X0
       grind)
    | (have i₁ := eq20 (M.op X2 X2) X3 X1
       have i₂ := eq19 X0 X1 X2
       grind)
    | exact superpose eq19 eq20
    | exact resolve eq20 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq134 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X2 (σ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq31 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq31 eq13
    | (have j1 := eq31 (σ X0) X2 X2
       grind)
    | exact resolve eq13 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ X0 ∨ (k X0 (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq139 X0 (M.op X2 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq139
    | (have j0 := eq139 X0 (M.op X2 X2)
       grind)
    | (have r₁ := eq139 (M.op (M.op X2 X2) (M.op X2 X2)) (M.op X2 X2)
       have r₂ := eq8 (M.op X2 X2) (M.op X2 X2) X2
       grind)
    | exact resolve eq139 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op X3 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17 (M.op X1 X1) X3 X2
       have i₂ := eq19 X1 (M.op X1 X1) X0
       grind)
    | (have i₁ := eq17 (M.op X1 X1) X3 X2
       have i₂ := eq19 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq19 eq17
    | exact resolve eq17 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) ≠ (M.op (M.op X2 X2) X1) ∨ (M.op (M.op X2 X2) X1) = (k (M.op (M.op X2 X2) X1) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq139 (M.op (M.op X2 X2) X1) X1
       have i₂ := eq17 X2 X1 X0
       grind)
    | exact superpose eq17 eq139
    | (have j0 := eq139 (M.op (M.op X2 X2) X1) X1
       grind)
    | (have r₁ := eq139 (M.op (M.op x x) X1) X1
       have r₂ := eq17 x X1 x
       grind)
    | exact resolve eq139 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op X3 X3) (M.op (M.op X2 X2) (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X1 (M.op (M.op X2 X2) (M.op X1 X1)) X3
       have i₂ := eq17 X2 (M.op X1 X1) X0
       grind)
    | exact superpose eq17 eq19
    | exact resolve eq19 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq191 : ∀ X1 X2 : G, (M.op (M.op X2 X2) X1) = (k (M.op (M.op X2 X2) X1) X1) := by
    intro X1 X2
    first
    | (have j0 := eq185 x X1 X2
       grind)
    | (have r₁ := eq185 x X1 x
       have r₂ := eq19 x X1 x
       grind)
    | (have r₁ := eq185 x X1 x
       have r₂ := eq19 x X1 x
       grind)
    | exact resolve eq185 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq380 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X1 X1)) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq139 X0 (M.op X1 X1)
       have i₂ := eq28 X0 X1 X2
       grind)
    | (have i₁ := eq139 X0 X0
       have i₂ := eq28 X0 X1 X2
       grind)
    | exact superpose eq28 eq139
    | (have j0 := eq139 X0 X0
       have j1 := eq28 X0 X1 X2
       grind)
    | exact resolve eq139 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq139
  have eq388 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X1)) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq380 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq380 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq380 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq598 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq29 x y
       grind)
    | exact superpose eq29 eq14
    | (have j1 := eq29 x x
       grind)
    | exact resolve eq14 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq600 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ X0)
       have i₂ := eq29 X0 X0
       grind)
    | exact superpose eq29 eq11
    | (have j0 := eq11 X1 (σ X0)
       have j1 := eq29 X0 X1
       grind)
    | (have r₁ := eq11 X0 (σ X0)
       have r₂ := eq29 X0 X1
       grind)
    | exact resolve eq11 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (σ X1)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (σ X1) (σ X0) X2
       have i₂ := eq29 X1 X0
       grind)
    | exact superpose eq29 eq8
    | (have j1 := eq29 X1 X1
       grind)
    | exact resolve eq8 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq637 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq29 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq641 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq600 X0 X1
       have j1 := eq11 X1 (σ X0)
       grind)
    | (have r₁ := eq600 X0 X1
       have r₂ := eq11 X0 (σ X0)
       grind)
    | exact resolve eq600 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq658 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq641 (τ X0) X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq641
    | (have j0 := eq641 (τ X0) X1
       grind)
    | exact resolve eq641 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq662 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq658 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq658
    | (have j0 := eq658 X0 X1
       grind)
    | exact resolve eq658 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq666 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq662 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq662
    | (have j0 := eq662 X0 X1
       grind)
    | exact resolve eq662 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq717 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq666 (τ X0) X1
       have i₂ := eq69 X0 X0
       grind)
    | exact superpose eq69 eq666
    | (have j0 := eq666 (τ X0) X1
       grind)
    | exact resolve eq666 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq2001 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq637 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq637
    | (have j0 := eq637 (τ X0)
       grind)
    | exact resolve eq637 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq2010 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2001 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2001
    | (have j0 := eq2001 X0
       grind)
    | exact resolve eq2001 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2001
  have eq2016 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2010 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2010
    | (have j0 := eq2010 X0
       grind)
    | exact resolve eq2010 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2010
  have eq6200 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq598
       have i₂ := eq31 x X0 y
       grind)
    | exact superpose eq31 eq598
    | (have j1 := eq31 x X0 x
       grind)
    | exact resolve eq598 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq598
  have eq6204 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq6200 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6200
  have eq6296 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq6204 (τ X0)
       grind)
    | exact superpose eq6204 eq15
    | exact resolve eq15 eq6204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq6204
  have eq6300 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq6296 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6296
    | exact resolve eq6296 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6296
  have eq6311 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq6300 X0
       have j1 := eq11 X0 (σ x)
       grind)
    | (have r₁ := eq6300 X0
       have r₂ := eq11 X0 (σ x)
       grind)
    | exact resolve eq6300 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6300
  have eq6489 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2016 (σ x)
       have i₂ := eq6311 (σ x)
       grind)
    | exact superpose eq6311 eq2016
    | (have j0 := eq2016 (σ x)
       grind)
    | (have r₁ := eq2016 (σ x)
       have r₂ := eq6311 (σ x)
       grind)
    | exact resolve eq2016 eq6311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6491 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq717 (σ x) X0
       have i₂ := eq6311 (σ x)
       grind)
    | exact superpose eq6311 eq717
    | (have j0 := eq717 (σ x) X0
       grind)
    | exact resolve eq717 eq6311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq6501 : ∀ X0 X1 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (k (σ x) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq388 (σ x) X1 X0
       have i₂ := eq6311 X0
       grind)
    | exact superpose eq6311 eq388
    | (have j0 := eq388 (σ x) X1 x
       grind)
    | exact resolve eq388 eq6311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388 eq6311
  have eq6514 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 := by
    intro X0
    first
    | (have j0 := eq6491 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6491
  have eq6516 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6489
  have eq6522 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq6514 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq6514
    | exact resolve eq6514 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6514
  have eq6625 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2016 x
       have i₂ := eq6522 x
       grind)
    | exact superpose eq6522 eq2016
    | (have j0 := eq2016 x
       grind)
    | (have r₁ := eq2016 x
       have r₂ := eq6522 x
       grind)
    | exact resolve eq2016 eq6522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6522
  have eq6650 : x = (M.op x x) := by grind
  clear eq6625
  have eq7002 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq6650
       grind)
    | exact superpose eq6650 eq8
    | exact resolve eq8 eq6650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7007 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1 x
       have i₂ := eq6650
       grind)
    | exact superpose eq6650 eq19
    | exact resolve eq19 eq6650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7030 : ∀ X0 : G, (M.op x X0) = (k (M.op x X0) X0) := by
    intro X0
    first
    | (have i₁ := eq191 x x
       have i₂ := eq6650
       grind)
    | exact superpose eq6650 eq191
    | exact resolve eq191 eq6650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq7055 : ∀ X0 X1 : G, (M.op x x) = (M.op X0 x) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 x x X1
       have i₂ := eq6650
       grind)
    | exact superpose eq6650 eq26
    | (have j0 := eq26 X0 X1 x X1
       grind)
    | exact resolve eq26 eq6650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq7067 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ x = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq7055 X0 X1
       have i₂ := eq6650
       grind)
    | exact superpose eq6650 eq7055
    | (have j0 := eq7055 X0 X1
       grind)
    | exact resolve eq7055 eq6650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7055
  have eq9024 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X3) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4)) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X1 X1) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq159 X0 X0 X3 (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4)
       have i₂ := eq95 X1 X2 (M.op X0 X0) X4
       grind)
    | (have i₁ := eq159 X0 X0 X2 (M.op (M.op X0 X0) X1)
       have i₂ := eq95 X0 X1 (M.op X0 X0) X3
       grind)
    | exact superpose eq95 eq159
    | exact resolve eq159 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq159
  have eq9073 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X3) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4)) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4) (M.op x (M.op (M.op X1 X1) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9024 X0 X1 X2 X3 X4
       have i₂ := eq7007 (M.op X0 X0) (M.op (M.op X1 X1) X2)
       grind)
    | exact superpose eq7007 eq9024
    | exact resolve eq9024 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9024
  have eq9189 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X3 X3) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4)) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4) (M.op x (M.op x X2))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq9073 X0 x X2 X3 X4
       have i₂ := eq7007 x X2
       grind)
    | exact superpose eq7007 eq9073
    | exact resolve eq9073 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9073
  have eq9305 : ∀ X0 X3 X4 : G, (M.op (M.op X3 X3) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4)) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4) (M.op x x)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9189 X0 x X3 X4
       have i₂ := eq7002 x x
       grind)
    | exact superpose eq7002 eq9189
    | exact resolve eq9189 eq7002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9189
  have eq9418 : ∀ X0 X3 X4 : G, (M.op (M.op X3 X3) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4)) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4) x) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9305 X0 X3 X4
       have i₂ := eq6650
       grind)
    | exact superpose eq6650 eq9305
    | exact resolve eq9305 eq6650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9305
  have eq9526 : ∀ X3 X4 : G, (M.op (M.op X3 X3) (M.op x X4)) = (M.op (M.op x X4) x) := by
    intro X3 X4
    first
    | (have i₁ := eq9418 x X3 x
       have i₂ := eq7007 (M.op x x) x
       grind)
    | exact superpose eq7007 eq9418
    | exact resolve eq9418 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9418
  have eq9632 : ∀ X4 : G, (M.op x (M.op x X4)) = (M.op (M.op x X4) x) := by
    intro X4
    first
    | (have i₁ := eq9526 x X4
       have i₂ := eq7007 x (M.op x X4)
       grind)
    | exact superpose eq7007 eq9526
    | exact resolve eq9526 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9526
  have eq9714 : ∀ X4 : G, (M.op x x) = (M.op (M.op x X4) x) := by
    intro X4
    first
    | (have i₁ := eq9632 X4
       have i₂ := eq7002 x X4
       grind)
    | exact superpose eq7002 eq9632
    | exact resolve eq9632 eq7002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9632
  have eq9775 : ∀ X4 : G, x = (M.op (M.op x X4) x) := by
    intro X4
    first
    | (have i₁ := eq9714 X4
       have i₂ := eq6650
       grind)
    | exact superpose eq6650 eq9714
    | exact resolve eq9714 eq6650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9714
  have eq9886 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op X1 X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq67 x x X1 X0
       have i₂ := eq9775 x
       grind)
    | exact superpose eq9775 eq67
    | exact resolve eq67 eq9775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq9775
  have eq9941 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq9886 X0 X1
       have i₂ := eq7007 X1 x
       grind)
    | exact superpose eq7007 eq9886
    | exact resolve eq9886 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9886
  have eq9970 : ∀ X0 X1 : G, x = (M.op (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9941 X0 X1
       have i₂ := eq6650
       grind)
    | exact superpose eq6650 eq9941
    | exact resolve eq9941 eq6650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9941
  have eq9982 : ∀ X1 : G, x = (M.op x (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq9970 x X1
       have i₂ := eq7007 x (M.op X1 X1)
       grind)
    | exact superpose eq7007 eq9970
    | exact resolve eq9970 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9970
  have eq14615 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op X2 X2)) = (M.op (σ X0) (M.op (M.op X3 X3) (M.op X2 X2))) ∨ (M.op (σ X0) (σ X4)) = (σ (k X4 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq190 X1 X2 X3 (σ X0)
       have i₂ := eq29 X0 X4
       grind)
    | exact superpose eq29 eq190
    | (have j1 := eq29 X0 X4
       grind)
    | exact resolve eq190 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq190
  have eq15228 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 X1) (M.op X2 X2)) = (M.op (σ X0) (M.op x (M.op X2 X2))) ∨ (M.op (σ X0) (σ X4)) = (σ (k X4 X0)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq14615 X0 X1 X2 x X4
       have i₂ := eq7007 x (M.op X2 X2)
       grind)
    | exact superpose eq7007 eq14615
    | (have j0 := eq14615 X0 X1 X2 x X4
       grind)
    | exact resolve eq14615 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14615
  have eq15381 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 X1) (M.op X2 X2)) = (M.op (σ X0) x) ∨ (M.op (σ X0) (σ X4)) = (σ (k X4 X0)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq15228 X0 X1 X2 X4
       have i₂ := eq9982 X2
       grind)
    | exact superpose eq9982 eq15228
    | (have j0 := eq15228 X0 X1 X2 X4
       grind)
    | exact resolve eq15228 eq9982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15228
  have eq15532 : ∀ X0 X2 X4 : G, (M.op x (M.op X2 X2)) = (M.op (σ X0) x) ∨ (M.op (σ X0) (σ X4)) = (σ (k X4 X0)) := by
    intro X0 X2 X4
    first
    | (have i₁ := eq15381 X0 x X2 X4
       have i₂ := eq7007 x (M.op X2 X2)
       grind)
    | exact superpose eq7007 eq15381
    | (have j0 := eq15381 X0 x X2 X4
       grind)
    | exact resolve eq15381 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15381
  have eq15675 : ∀ X0 X4 : G, (M.op (σ X0) (σ X4)) = (σ (k X4 X0)) ∨ x = (M.op (σ X0) x) := by
    intro X0 X4
    first
    | (have i₁ := eq15532 X0 x X4
       have i₂ := eq9982 x
       grind)
    | exact superpose eq9982 eq15532
    | (have j0 := eq15532 X0 x X4
       grind)
    | exact resolve eq15532 eq9982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15532
  have eq19463 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1 (σ x)
       have i₂ := eq6516
       grind)
    | exact superpose eq6516 eq19
    | exact resolve eq19 eq6516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq19524 : x = (M.op x (σ x)) := by
    first
    | (have i₁ := eq9982 (σ x)
       have i₂ := eq6516
       grind)
    | exact superpose eq6516 eq9982
    | exact resolve eq9982 eq6516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9982
  have eq19532 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq148 (σ x) (σ x) X0
       have i₂ := eq6516
       grind)
    | exact superpose eq6516 eq148
    | (have j0 := eq148 (σ x) x X0
       grind)
    | exact resolve eq148 eq6516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq19549 : ∀ X0 : G, (σ x) = (k (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq19532 X0
       have j1 := eq6501 X0 X0
       grind)
    | (have r₁ := eq19532 X0
       have r₂ := eq6501 (σ x) x
       grind)
    | exact resolve eq19532 eq6501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6501 eq19532
  have eq19597 : ∀ X1 : G, (M.op x X1) = (M.op (σ x) X1) := by
    intro X1
    first
    | (have i₁ := eq19463 x X1
       have i₂ := eq7007 x X1
       grind)
    | exact superpose eq7007 eq19463
    | exact resolve eq19463 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19463
  have eq24810 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq19597 (σ y)
       grind)
    | exact superpose eq19597 eq14
    | exact resolve eq14 eq19597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24811 : (σ x) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq6516
       have i₂ := eq19597 (σ x)
       grind)
    | exact superpose eq19597 eq6516
    | exact resolve eq6516 eq19597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19597
  have eq25080 : x = (σ x) := by
    first
    | (have i₁ := eq24811
       have i₂ := eq19524
       grind)
    | exact superpose eq19524 eq24811
    | exact resolve eq24811 eq19524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19524 eq24811
  have eq33070 : ∀ X0 : G, (τ (σ x)) = (k x (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq38 x (M.op X0 X0)
       have i₂ := eq19549 X0
       grind)
    | exact superpose eq19549 eq38
    | exact resolve eq38 eq19549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq19549
  have eq33084 : ∀ X0 : G, x = (k x (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq33070 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq33070
    | exact resolve eq33070 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33070
  have eq43720 : ∀ X0 : G, (τ (M.op x (σ X0))) = (k (τ (M.op x (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq24 (M.op x (σ X0)) X0
       have i₂ := eq7030 (σ X0)
       grind)
    | exact superpose eq7030 eq24
    | exact resolve eq24 eq7030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq7030
  have eq89782 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (σ X1)) = (σ (k (k X2 X1) X1)) ∨ (k X3 (σ X1)) = X3 ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq134 X1 (k X2 X1) X3
       have i₂ := eq611 X2 X1 X0
       grind)
    | exact superpose eq611 eq134
    | (have j0 := eq134 X1 X1 X3
       have j1 := eq611 X0 X1 X2
       grind)
    | exact resolve eq134 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq611
  have eq89848 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (σ X1)) = (σ (k (k X2 X1) X1)) ∨ (k X3 (σ X1)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq89782 X0 X1 X2 X3
       have j1 := eq11 X3 (σ X1)
       grind)
    | (have r₁ := eq89782 X0 X1 X2 X3
       have r₂ := eq11 X0 (σ X1)
       grind)
    | exact resolve eq89782 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89782
  have eq90014 : ∀ X1 X2 X3 : G, (M.op x (σ X1)) = (σ (k (k X2 X1) X1)) ∨ (k X3 (σ X1)) = X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq89848 x X1 X2 X3
       have i₂ := eq7007 x (σ X1)
       grind)
    | exact superpose eq7007 eq89848
    | (have j0 := eq89848 x X1 X2 X3
       grind)
    | exact resolve eq89848 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7007 eq89848
  have eq259053 : ∀ X0 : G, x = (k x (τ (σ (k X0 X0)))) ∨ x = (M.op (σ X0) x) := by
    intro X0
    first
    | (have i₁ := eq33084 (σ X0)
       have i₂ := eq15675 X0 X0
       grind)
    | exact superpose eq15675 eq33084
    | (have j1 := eq15675 X0 x
       grind)
    | exact resolve eq33084 eq15675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15675 eq33084
  have eq259102 : ∀ X0 : G, x = (k x (k X0 X0)) ∨ x = (M.op (σ X0) x) := by
    intro X0
    first
    | (have i₁ := eq259053 X0
       have i₂ := eq9 (k X0 X0)
       grind)
    | exact superpose eq9 eq259053
    | (have j0 := eq259053 X0
       grind)
    | exact resolve eq259053 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259053
  have eq259754 : ∀ X0 : G, x = (k x (τ (k X0 X0))) ∨ x = (M.op (σ (τ X0)) x) := by
    intro X0
    first
    | (have i₁ := eq259102 (τ X0)
       have i₂ := eq69 X0 X0
       grind)
    | exact superpose eq69 eq259102
    | (have j0 := eq259102 (τ X0)
       grind)
    | exact resolve eq259102 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259102
  have eq259775 : ∀ X0 : G, x = (k x (τ (k X0 X0))) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq259754 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq259754
    | (have j0 := eq259754 X0
       grind)
    | exact resolve eq259754 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259754
  have eq264392 : ∀ X0 : G, (σ x) = (k (σ x) (k X0 X0)) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq16 (k X0 X0) x
       have i₂ := eq259775 X0
       grind)
    | exact superpose eq259775 eq16
    | (have j1 := eq259775 X0
       grind)
    | exact resolve eq16 eq259775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259775
  have eq264403 : ∀ X0 : G, x = (k x (k X0 X0)) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq264392 X0
       have i₂ := eq25080
       grind)
    | exact superpose eq25080 eq264392
    | (have j0 := eq264392 X0
       grind)
    | exact resolve eq264392 eq25080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25080 eq264392
  have eq265184 : ∀ X0 : G, x = (M.op (k X0 X0) x) ∨ x = (M.op (k X0 X0) x) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq7067 (k X0 X0) x
       have i₂ := eq264403 X0
       grind)
    | exact superpose eq264403 eq7067
    | (have j0 := eq7067 (k X0 X0) x
       have j1 := eq264403 (k X0 X0)
       grind)
    | exact resolve eq7067 eq264403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7067 eq264403
  have eq265188 : ∀ X0 : G, x = (M.op (k X0 X0) x) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq265184 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265184
  have eq284951 : ∀ X0 X1 X2 : G, (M.op x (σ (τ X1))) = (σ (k (τ (k X0 X1)) (τ X1))) ∨ (k X2 (σ (τ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq90014 (τ X1) (τ X0) X2
       have i₂ := eq69 X1 X0
       grind)
    | exact superpose eq69 eq90014
    | (have j0 := eq90014 (τ X1) X2 X2
       grind)
    | exact resolve eq90014 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq90014
  have eq284994 : ∀ X0 X1 X2 : G, (M.op x (σ (τ X1))) = (k (σ (τ (k X0 X1))) X1) ∨ (k X2 (σ (τ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq284951 X0 X1 X2
       have i₂ := eq16 X1 (τ (k X0 X1))
       grind)
    | exact superpose eq16 eq284951
    | (have j0 := eq284951 X0 X1 X2
       grind)
    | exact resolve eq284951 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq284951
  have eq285011 : ∀ X0 X1 X2 : G, (k (k X0 X1) X1) = (M.op x (σ (τ X1))) ∨ (k X2 (σ (τ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq284994 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq284994
    | (have j0 := eq284994 X0 X1 X2
       grind)
    | exact resolve eq284994 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284994
  have eq285021 : ∀ X0 X1 X2 : G, (k (k X0 X1) X1) = (M.op x X1) ∨ (k X2 (σ (τ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq285011 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq285011
    | (have j0 := eq285011 X0 X1 X2
       grind)
    | exact resolve eq285011 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285011
  have eq285026 : ∀ X0 X1 X2 : G, (k X2 X1) = X2 ∨ (k (k X0 X1) X1) = (M.op x X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq285021 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq285021
    | (have j0 := eq285021 X0 X1 X2
       grind)
    | exact resolve eq285021 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285021
  have eq291306 : ∀ X0 X1 : G, (M.op x X0) = (k (τ (M.op x (σ X0))) X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq285026 (τ (M.op x (σ X0))) X0 X1
       have i₂ := eq43720 X0
       grind)
    | exact superpose eq43720 eq285026
    | (have j0 := eq285026 X0 X0 X1
       grind)
    | exact resolve eq285026 eq43720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285026
  have eq291437 : ∀ X0 X1 : G, (M.op x X0) = (τ (M.op x (σ X0))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq291306 X0 X1
       have i₂ := eq43720 X0
       grind)
    | exact superpose eq43720 eq291306
    | (have j0 := eq291306 X0 X1
       grind)
    | exact resolve eq291306 eq43720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43720 eq291306
  have eq350747 : ∀ X0 X1 : G, (σ (M.op x X0)) = (M.op x (σ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op x (σ X0))
       have i₂ := eq291437 X0 X1
       grind)
    | exact superpose eq291437 eq10
    | (have j1 := eq291437 X0 X1
       grind)
    | exact resolve eq10 eq291437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291437
  have eq354219 : ∀ X0 : G, (M.op x (σ y)) ≠ (M.op x (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq24810
       have i₂ := eq350747 y X0
       grind)
    | exact superpose eq350747 eq24810
    | (have j1 := eq350747 y X0
       grind)
    | (have r₁ := eq24810
       have r₂ := eq350747 y x
       grind)
    | exact resolve eq24810 eq350747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24810 eq350747
  have eq354273 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq354219 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354219
  have eq354486 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2016 y
       have i₂ := eq354273 y
       grind)
    | exact superpose eq354273 eq2016
    | (have j0 := eq2016 y
       grind)
    | (have r₁ := eq2016 y
       have r₂ := eq354273 y
       grind)
    | exact resolve eq2016 eq354273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2016
  have eq354564 : x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq265188 y
       have i₂ := eq354273 y
       grind)
    | exact superpose eq354273 eq265188
    | (have j0 := eq265188 y
       grind)
    | exact resolve eq265188 eq354273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265188 eq354273
  have eq354817 : x = (M.op y x) := by grind
  clear eq354564
  have eq354818 : y = (M.op y y) := by grind
  clear eq354486
  have eq355044 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq7002 y x
       have i₂ := eq354817
       grind)
    | exact superpose eq354817 eq7002
    | exact resolve eq7002 eq354817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355072 : x = (M.op x y) := by
    first
    | (have i₁ := eq355044
       have i₂ := eq354817
       grind)
    | exact superpose eq354817 eq355044
    | exact resolve eq355044 eq354817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354817 eq355044
  have eq355526 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq7002 y y
       have i₂ := eq354818
       grind)
    | exact superpose eq354818 eq7002
    | exact resolve eq7002 eq354818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7002
  have eq355553 : y = (M.op x y) := by
    first
    | (have i₁ := eq355526
       have i₂ := eq354818
       grind)
    | exact superpose eq354818 eq355526
    | exact resolve eq355526 eq354818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354818 eq355526
  have eq355781 : x = y := by
    first
    | (have i₁ := eq355553
       have i₂ := eq355072
       grind)
    | exact superpose eq355072 eq355553
    | exact resolve eq355553 eq355072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355072 eq355553
  have eq356245 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq355781
       grind)
    | exact superpose eq355781 eq14
    | exact resolve eq14 eq355781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355781
  have eq356253 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq356245
       have i₂ := eq6650
       grind)
    | exact superpose eq6650 eq356245
    | exact resolve eq356245 eq6650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6650 eq356245
  have eq356255 : False := by grind
  exact eq356255
