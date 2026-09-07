import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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
