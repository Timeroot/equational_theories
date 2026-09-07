import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation839`: `x = x ◇ ((y ◇ x) ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pyx_x_pyx_Equation839 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law839 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law839.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X1))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op (M.op (M.op X2 X0) (M.op X3 X2)) X1) X0)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 (M.op (M.op X2 X0) (M.op X3 X2)) X0
       have i₂ := eq8 X0 X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X0 X1) (M.op X1 (M.op (M.op X0 X1) X2))
       have i₂ := eq8 (M.op (M.op X0 X1) X2) X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 (M.op (M.op x x) X0) X1
       have i₂ := eq23 x x X0
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq48 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X1))) = X1 ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X1 X1
       have i₂ := eq12 (M.op X1 X1) X0
       grind)
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq12 (M.op x X1) (M.op X1 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 (M.op X1 X1) X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq53 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq56 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 (M.op X1 X0)
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq85 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X1)
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq11
    | (have j0 := eq11 X1 X0
       grind)
    | (have r₁ := eq11 X1 (M.op X1 X1)
       have r₂ := eq56 X1 X1
       grind)
    | exact resolve eq11 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq53
    | exact resolve eq53 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq53 X1 (τ X0)
       grind)
    | exact superpose eq53 eq16
    | (have j1 := eq53 X1 (τ X0)
       grind)
    | exact resolve eq16 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq94 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq102 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq12 X1 (σ X0)
       grind)
    | exact superpose eq12 eq20
    | (have j1 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq20 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq117 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X2 X3) (M.op X4 X2)) X0) X3) X5) X0) X1) X5)) = X1 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq22 X5 X1 (M.op (M.op (M.op (M.op X2 X3) (M.op X4 X2)) X0) X3) X0
       have i₂ := eq22 X3 X0 X2 X4
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (M.op X0 (M.op X1 X1)) X2) X1)) = X2 ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X1 X2 X1 X1
       have i₂ := eq12 (M.op X1 X1) X0
       grind)
    | (have i₁ := eq22 X0 X1 X2 x
       have i₂ := eq12 (M.op x X2) (M.op X2 X0)
       grind)
    | exact superpose eq12 eq22
    | (have j1 := eq12 (M.op X1 X1) X0
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq336 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq48 x x
       have i₂ := eq25 x x
       grind)
    | exact superpose eq25 eq48
    | exact resolve eq48 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq845 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op (σ (k X0 X1)) (M.op X2 (σ X1)))) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (σ X0) (σ X1) X2
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq8
    | (have j1 := eq50 X1 X0
       grind)
    | exact resolve eq8 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq855 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X1) (σ X0)
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq25
    | (have j1 := eq50 X1 X0
       grind)
    | exact resolve eq25 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq917 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq918 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1043 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X1 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq85 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq85
    | (have j0 := eq85 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq85 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq85 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq85 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1054 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq85 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq1057 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1043 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043
  have eq1103 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq71 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq1054 (σ X0)
       grind)
    | exact superpose eq1054 eq71
    | exact resolve eq71 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq1104 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq15 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq1054 (τ X0)
       grind)
    | exact superpose eq1054 eq15
    | exact resolve eq15 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq1054
  have eq1105 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1104 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1104
    | exact resolve eq1104 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq1106 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1103 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1103
    | exact resolve eq1103 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq1548 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq93 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq93
    | exact resolve eq93 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq1605 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1548 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1548
    | (have j0 := eq1548 X0 X1
       grind)
    | exact resolve eq1548 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548
  have eq1889 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) ∨ (k (M.op X1 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1057 X1 (M.op X0 X1)
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq1057
    | exact resolve eq1057 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq1948 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq89 y x
       grind)
    | exact superpose eq89 eq14
    | (have j1 := eq89 y x
       grind)
    | exact resolve eq14 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1962 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X1) (σ X0)
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq25
    | (have j1 := eq89 X0 X1
       grind)
    | exact resolve eq25 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4360 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq918 (τ X0) (τ X1)
       have i₂ := eq96 X0 X1
       grind)
    | exact superpose eq96 eq918
    | exact resolve eq918 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4386 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4360 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4360
    | (have j0 := eq4360 X0 X1
       grind)
    | exact resolve eq4360 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4360
  have eq4392 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4386 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq4386
    | (have j0 := eq4386 X0 X1
       grind)
    | exact resolve eq4386 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4386
  have eq4394 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4392 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4392
    | (have j0 := eq4392 X0 X1
       grind)
    | exact resolve eq4392 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4392
  have eq4395 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4394 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4394
    | (have j0 := eq4394 X0 X1
       grind)
    | exact resolve eq4394 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4394
  have eq4396 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4395 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq4395
    | (have j0 := eq4395 X0 X1
       grind)
    | exact resolve eq4395 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4395
  have eq4453 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq917 (τ X1) (τ X0)
       have i₂ := eq96 X1 X0
       grind)
    | exact superpose eq96 eq917
    | (have j0 := eq917 (τ X1) (τ X0)
       grind)
    | exact resolve eq917 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq4479 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4453 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4453
    | (have j0 := eq4453 X0 X1
       grind)
    | exact resolve eq4453 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4453
  have eq4484 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4479 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq4479
    | (have j0 := eq4479 X0 X1
       grind)
    | exact resolve eq4479 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4479
  have eq4485 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4484 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4484
    | (have j0 := eq4484 X0 X1
       grind)
    | exact resolve eq4484 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4484
  have eq4486 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4485 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4485
    | (have j0 := eq4485 X0 X1
       grind)
    | exact resolve eq4485 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4485
  have eq4741 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq4486 X0 (σ (M.op (τ X0) (τ X0)))
       have i₂ := eq1105 X0
       grind)
    | exact superpose eq1105 eq4486
    | (have j0 := eq4486 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | exact resolve eq4486 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4743 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq4486 X0 (τ (M.op (σ X0) (σ X0)))
       have i₂ := eq1106 X0
       grind)
    | exact superpose eq1106 eq4486
    | (have j0 := eq4486 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact resolve eq4486 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5520 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq1948
       have i₂ := eq1605 x y
       grind)
    | exact superpose eq1605 eq1948
    | (have j1 := eq1605 x y
       grind)
    | (have r₁ := eq1948
       have r₂ := eq1605 x y
       grind)
    | exact resolve eq1948 eq1605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1605 eq1948
  have eq5521 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by grind
  clear eq5520
  have eq5803 : (M.op x y) = (τ (σ y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq5521
       grind)
    | exact superpose eq5521 eq9
    | exact resolve eq9 eq5521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5521
  have eq5847 : y = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq5803
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq5803
    | exact resolve eq5803 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5803
  have eq5848 : y = (k y x) := by
    first
    | (have j1 := eq94 y x
       grind)
    | (have r₁ := eq5847
       have r₂ := eq94 y x
       grind)
    | exact resolve eq5847 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq5847
  have eq6154 : y ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq4486 y x
       have i₂ := eq5848
       grind)
    | exact superpose eq5848 eq4486
    | (have j0 := eq4486 y x
       grind)
    | exact resolve eq4486 eq5848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4486
  have eq7243 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X1) X0)) = X1 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq126 X1 X1 x
       have i₂ := eq25 X1 X1
       grind)
    | exact superpose eq25 eq126
    | exact resolve eq126 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq9684 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7243 X0 (M.op X1 X0)
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq7243
    | (have j0 := eq7243 X0 X1
       grind)
    | exact resolve eq7243 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7243
  have eq10818 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (M.op (σ (τ (k X0 X1))) (M.op X2 (σ (τ X1))))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq845 (τ X0) (τ X1) X2
       have i₂ := eq96 X1 X0
       grind)
    | exact superpose eq96 eq845
    | (have j0 := eq845 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq845 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq10978 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (M.op (σ (τ (k X0 X1))) (M.op X2 X1))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10818 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq10818
    | (have j0 := eq10818 X0 X1 X2
       grind)
    | exact resolve eq10818 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10818
  have eq10989 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (M.op (k X0 X1) (M.op X2 X1))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10978 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq10978
    | (have j0 := eq10978 X0 X1 X2
       grind)
    | exact resolve eq10978 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10978
  have eq10992 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (k X0 X1) (M.op X2 X1))) = X0 ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10989 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10989
    | (have j0 := eq10989 X0 X1 X2
       grind)
    | exact resolve eq10989 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10989
  have eq10993 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 (M.op (k X0 X1) (M.op X2 X1))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10992 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10992
    | (have j0 := eq10992 X0 X1 X2
       grind)
    | exact resolve eq10992 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10992
  have eq10994 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (k X0 X1) (M.op X2 X1))) = X0 ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10993 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq10993
    | (have j0 := eq10993 X0 X1 X2
       grind)
    | exact resolve eq10993 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10993
  have eq11957 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1889 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1889
  have eq18258 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1962 (τ X1) (τ X0)
       have i₂ := eq96 X0 X1
       grind)
    | exact superpose eq96 eq1962
    | exact resolve eq1962 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18440 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18258 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq18258
    | (have j0 := eq18258 X0 X1
       grind)
    | exact resolve eq18258 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18258
  have eq18455 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18440 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18440
    | (have j0 := eq18440 X0 X1
       grind)
    | exact resolve eq18440 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18440
  have eq18461 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (M.op X0 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18455 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq18455
    | (have j0 := eq18455 X0 X1
       grind)
    | exact resolve eq18455 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18455
  have eq18462 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18461 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18461
    | (have j0 := eq18461 X0 X1
       grind)
    | exact resolve eq18461 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18461
  have eq18903 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ (k X0 X1))) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18462 (τ X1) (τ X0)
       have i₂ := eq96 X0 X1
       grind)
    | exact superpose eq96 eq18462
    | exact resolve eq18462 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18462
  have eq33838 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq102 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq102
    | exact resolve eq102 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq34455 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq33838 X0 X1
       have i₂ := eq96 X0 X1
       grind)
    | exact superpose eq96 eq33838
    | (have j0 := eq33838 X0 X1
       grind)
    | exact resolve eq33838 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq33838
  have eq35311 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq336 X1
       have i₂ := eq34455 X1 X1
       grind)
    | (have i₁ := eq336 X1
       have i₂ := eq34455 X0 X1
       grind)
    | exact superpose eq34455 eq336
    | (have j1 := eq34455 X0 X1
       grind)
    | exact resolve eq336 eq34455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336 eq34455
  have eq35686 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = X1 ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq35311 X0 X1
       have j1 := eq11957 X0 X1
       grind)
    | (have r₁ := eq35311 X0 X1
       have r₂ := eq11957 X0 X1
       grind)
    | exact resolve eq35311 eq11957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11957 eq35311
  have eq54594 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k (M.op X0 X0) X1) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4396 (M.op X0 X0) X1
       have i₂ := eq9684 X0 X0
       grind)
    | exact superpose eq9684 eq4396
    | (have j0 := eq4396 (M.op X0 X0) X1
       have j1 := eq9684 X0 X1
       grind)
    | exact resolve eq4396 eq9684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4396 eq9684
  have eq54810 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq54594 X0 X1
       have j1 := eq53 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq54594 X0 X1
       have r₂ := eq53 (M.op X0 X0) X1
       grind)
    | exact resolve eq54594 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq54594
  have eq55908 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10994 X0 X1 (M.op (M.op (M.op (M.op (M.op (M.op (M.op x x) (M.op x x)) x) x) X1) x) (k X0 X1))
       have i₂ := eq117 x (k X0 X1) x x x X1
       grind)
    | exact superpose eq117 eq10994
    | (have j0 := eq10994 X0 X1 x
       grind)
    | exact resolve eq10994 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq10994
  have eq57058 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (M.op (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq55908 X0 (σ (M.op (τ X0) (τ X0)))
       have i₂ := eq1105 X0
       grind)
    | exact superpose eq1105 eq55908
    | (have j0 := eq55908 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | exact resolve eq55908 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105
  have eq57061 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (M.op (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq55908 X0 (τ (M.op (σ X0) (σ X0)))
       have i₂ := eq1106 X0
       grind)
    | exact superpose eq1106 eq55908
    | (have j0 := eq55908 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact resolve eq55908 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57092 : y = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq55908 y x
       have i₂ := eq5848
       grind)
    | exact superpose eq5848 eq55908
    | (have j0 := eq55908 y x
       grind)
    | exact resolve eq55908 eq5848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55908
  have eq57385 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq57092
       have r₂ := eq6154
       grind)
    | exact resolve eq57092 eq6154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6154 eq57092
  have eq57390 : ∀ X0 : G, (M.op X0 X0) = (M.op (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have j0 := eq57061 X0
       have j1 := eq4743 X0
       grind)
    | (have r₁ := eq57061 X0
       have r₂ := eq4743 X0
       grind)
    | exact resolve eq57061 eq4743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4743 eq57061
  have eq57393 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have j0 := eq57058 X0
       have j1 := eq4741 X0
       grind)
    | (have r₁ := eq57058 X0
       have r₂ := eq4741 X0
       grind)
    | exact resolve eq57058 eq4741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4741 eq57058
  have eq61588 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq57390 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq57390
    | exact resolve eq57390 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61820 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (τ (M.op X0 X0)) = (τ (k X0 (τ (M.op (σ X0) (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq35686 (τ (M.op (σ X0) (σ X0))) X0
       have i₂ := eq57390 X0
       grind)
    | exact superpose eq57390 eq35686
    | (have j0 := eq35686 X0 X0
       grind)
    | exact resolve eq35686 eq57390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35686 eq57390
  have eq61871 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq61820 X0
       have i₂ := eq1106 X0
       grind)
    | exact superpose eq1106 eq61820
    | (have j0 := eq61820 X0
       grind)
    | exact resolve eq61820 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106 eq61820
  have eq62626 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq57393 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq57393
    | exact resolve eq57393 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57393
  have eq64920 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq62626 y
       have i₂ := eq57385
       grind)
    | exact superpose eq57385 eq62626
    | exact resolve eq62626 eq57385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62626
  have eq66320 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op (σ y) (σ y)) (M.op X0 (σ (M.op x y))))) := by
    intro X0
    first
    | (have i₁ := eq8 (σ y) (σ (M.op x y)) X0
       have i₂ := eq64920
       grind)
    | exact superpose eq64920 eq8
    | exact resolve eq8 eq64920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68591 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq18903 (M.op X0 X0) X0
       have i₂ := eq61871 X0
       grind)
    | exact superpose eq61871 eq18903
    | (have j1 := eq61871 X0
       grind)
    | exact resolve eq18903 eq61871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18903 eq61871
  have eq68607 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq68591 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68591
  have eq68616 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68607 X0
       have i₂ := eq61588 X0
       grind)
    | exact superpose eq61588 eq68607
    | (have j0 := eq68607 X0
       grind)
    | exact resolve eq68607 eq61588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61588 eq68607
  have eq91480 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq68616 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq68616
    | exact resolve eq68616 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68616
  have eq102492 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq855 y x
       have i₂ := eq5848
       grind)
    | exact superpose eq5848 eq855
    | (have j0 := eq855 y x
       grind)
    | exact resolve eq855 eq5848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq104633 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq54810 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54810
  have eq104634 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq104633 X0
       grind)
    | (have r₁ := eq104633 X0
       have r₂ := eq25 X0 X0
       grind)
    | exact resolve eq104633 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104633
  have eq104753 : y = (k (M.op x y) y) := by
    first
    | (have i₁ := eq104634 y
       have i₂ := eq57385
       grind)
    | exact superpose eq57385 eq104634
    | exact resolve eq104634 eq57385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104634
  have eq104917 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1962 (M.op x y) y
       have i₂ := eq104753
       grind)
    | exact superpose eq104753 eq1962
    | exact resolve eq1962 eq104753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1962 eq104753
  have eq104956 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq104917
       have i₂ := eq64920
       grind)
    | exact superpose eq64920 eq104917
    | exact resolve eq104917 eq64920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104917
  have eq120780 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ X0))
       have i₂ := eq91480 X0
       grind)
    | exact superpose eq91480 eq10
    | (have j1 := eq91480 X0
       grind)
    | exact resolve eq10 eq91480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91480
  have eq122723 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ X0))
       have i₂ := eq120780 X0
       grind)
    | exact superpose eq120780 eq10
    | (have j1 := eq120780 X0
       grind)
    | exact resolve eq10 eq120780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120780
  have eq123091 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ (M.op y y)) (M.op X0 (σ (M.op x y))))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq66320 X0
       have i₂ := eq122723 y
       grind)
    | exact superpose eq122723 eq66320
    | (have j1 := eq122723 y
       grind)
    | exact resolve eq66320 eq122723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66320 eq122723
  have eq123164 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y))))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq123091 X0
       have i₂ := eq57385
       grind)
    | exact superpose eq57385 eq123091
    | exact resolve eq123091 eq57385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57385 eq123091
  have eq123192 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq123164 x
       have i₂ := eq25 x (σ (M.op x y))
       grind)
    | exact superpose eq25 eq123164
    | exact resolve eq123164 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123164
  have eq124964 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq25 (σ y) (σ (M.op x y))
       have i₂ := eq123192
       grind)
    | exact superpose eq123192 eq25
    | exact resolve eq25 eq123192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq123192
  have eq124987 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq124964
       have i₂ := eq64920
       grind)
    | exact superpose eq64920 eq124964
    | exact resolve eq124964 eq64920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64920 eq124964
  have eq129228 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq102492
       have i₂ := eq104956
       grind)
    | exact superpose eq104956 eq102492
    | exact resolve eq102492 eq104956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104956
  have eq129239 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq124987
       have i₂ := eq102492
       grind)
    | exact superpose eq102492 eq124987
    | exact resolve eq124987 eq102492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124987
  have eq129298 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq102492
  have eq129302 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq129228
  have eq129324 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq129239
       have r₂ := eq129298
       grind)
    | exact resolve eq129239 eq129298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129239 eq129298
  have eq129333 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq129302
       have r₂ := eq14
       grind)
    | exact resolve eq129302 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129302
  have eq129347 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq129324
       have r₂ := eq14
       grind)
    | exact resolve eq129324 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129324
  have eq129392 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 (M.op x y) X0
       have i₂ := eq129333
       grind)
    | exact superpose eq129333 eq13
    | exact resolve eq13 eq129333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129408 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (σ (k (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq89 (M.op x y) x
       have i₂ := eq129333
       grind)
    | exact superpose eq129333 eq89
    | exact resolve eq89 eq129333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq129426 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ (σ (k (M.op x y) X0)) ∨ (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq918 X0 (M.op x y)
       have i₂ := eq129333
       grind)
    | exact superpose eq129333 eq918
    | exact resolve eq918 eq129333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918
  have eq129553 : ∀ X0 : G, (σ y) ≠ (σ (k (M.op x y) X0)) ∨ (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq129426 X0
       have i₂ := eq129347
       grind)
    | exact superpose eq129347 eq129426
    | (have j0 := eq129426 X0
       grind)
    | exact resolve eq129426 eq129347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129347 eq129426
  have eq129576 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (σ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq129392 X0
       have i₂ := eq13 y X0
       grind)
    | exact superpose eq13 eq129392
    | exact resolve eq129392 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129392
  have eq129596 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq129553 X0
       have j1 := eq129408 X0
       grind)
    | (have r₁ := eq129553 X0
       have r₂ := eq129408 X0
       grind)
    | exact resolve eq129553 eq129408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129408 eq129553
  have eq129607 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq129596 X0
       have i₂ := eq129576 X0
       grind)
    | exact superpose eq129576 eq129596
    | exact resolve eq129596 eq129576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129576 eq129596
  have eq134050 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq129607 x
       grind)
    | exact superpose eq129607 eq14
    | exact resolve eq14 eq129607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129607
  have eq134551 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq134050
       have i₂ := eq5848
       grind)
    | exact superpose eq5848 eq134050
    | exact resolve eq134050 eq5848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5848 eq134050
  have eq134760 : False := by grind
  exact eq134760

/-- `Equation840`: `x = x ◇ ((y ◇ x) ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pyx_x_pyx_Equation840 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law840 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law840.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq22 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq8 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 (M.op X1 X0)
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq43 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X1))) = X1 ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X1 X1
       have i₂ := eq12 (M.op X1 X1) X0
       grind)
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq12 (M.op x x) (M.op X1 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 (M.op X1 X1) X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq47 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X1)
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq11
    | (have j0 := eq11 X1 X0
       grind)
    | (have r₁ := eq11 X1 (M.op X1 X1)
       have r₂ := eq24 X1 X1
       grind)
    | exact resolve eq11 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
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
  have eq68 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq47
    | exact resolve eq47 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq47 X1 (τ X0)
       grind)
    | exact superpose eq47 eq16
    | (have j1 := eq47 X1 (τ X0)
       grind)
    | exact resolve eq16 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X2 X2))) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X1 (M.op X0 X0)) X0 X2
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq8
    | (have j1 := eq43 X1 X0
       grind)
    | exact resolve eq8 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq437 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) (σ X0)
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq22
    | (have j1 := eq44 X1 X0
       grind)
    | exact resolve eq22 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq484 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq485 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq516 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq54 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq606 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq64 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq516 (σ X0)
       grind)
    | exact superpose eq516 eq64
    | exact resolve eq64 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq607 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq15 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq516 (τ X0)
       grind)
    | exact superpose eq516 eq15
    | exact resolve eq15 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq608 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq607 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq607
    | exact resolve eq607 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq609 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq606 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq606
    | exact resolve eq606 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq666 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq15 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq608 (τ X0)
       grind)
    | exact superpose eq608 eq15
    | exact resolve eq15 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq667 : ∀ X0 : G, (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq666 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq666
    | exact resolve eq666 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq736 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op (σ (σ X0)) (σ (σ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq64 X0 (τ (M.op (σ (σ X0)) (σ (σ X0))))
       have i₂ := eq609 (σ X0)
       grind)
    | exact superpose eq609 eq64
    | exact resolve eq64 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq741 : ∀ X0 : G, (k X0 (τ (τ (M.op (σ (σ X0)) (σ (σ X0)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq736 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq736
    | exact resolve eq736 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq924 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq84 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq84
    | exact resolve eq84 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq969 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq924 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq924
    | (have j0 := eq924 X0 X1
       grind)
    | exact resolve eq924 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq1245 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq79 y x
       grind)
    | exact superpose eq79 eq14
    | (have j1 := eq79 y x
       grind)
    | exact resolve eq14 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1253 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) (σ X0)
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq22
    | (have j1 := eq79 X0 X1
       grind)
    | exact resolve eq22 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2699 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq485 (τ X0) (τ X1)
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq485
    | exact resolve eq485 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2725 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2699 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2699
    | (have j0 := eq2699 X0 X1
       grind)
    | exact resolve eq2699 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2699
  have eq2731 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2725 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq2725
    | (have j0 := eq2725 X0 X1
       grind)
    | exact resolve eq2725 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725
  have eq2733 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2731 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2731
    | (have j0 := eq2731 X0 X1
       grind)
    | exact resolve eq2731 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2731
  have eq2734 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2733 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2733
    | (have j0 := eq2733 X0 X1
       grind)
    | exact resolve eq2733 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2733
  have eq2735 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2734 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq2734
    | (have j0 := eq2734 X0 X1
       grind)
    | exact resolve eq2734 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2734
  have eq2793 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq437 X0 (M.op X0 X0)
       have i₂ := eq516 X0
       grind)
    | exact superpose eq516 eq437
    | (have j0 := eq437 X0 (M.op X0 X0)
       grind)
    | exact resolve eq437 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2806 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq437 (τ X0) (τ X1)
       have i₂ := eq68 X1 X0
       grind)
    | exact superpose eq68 eq437
    | (have j0 := eq437 (τ X0) (τ X1)
       grind)
    | exact resolve eq437 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2859 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2806 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq2806
    | (have j0 := eq2806 X0 X1
       grind)
    | exact resolve eq2806 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2806
  have eq2866 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2859 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2859
    | (have j0 := eq2859 X0 X1
       grind)
    | exact resolve eq2859 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2859
  have eq2868 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2866 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2866
    | (have j0 := eq2866 X0 X1
       grind)
    | exact resolve eq2866 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2866
  have eq2869 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2868 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2868
    | (have j0 := eq2868 X0 X1
       grind)
    | exact resolve eq2868 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2868
  have eq2908 : ∀ X0 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq484 (M.op X0 X0) X0
       have i₂ := eq516 X0
       grind)
    | exact superpose eq516 eq484
    | (have j0 := eq484 (M.op X0 X0) X0
       grind)
    | exact resolve eq484 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq2918 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq484 (τ X1) (τ X0)
       have i₂ := eq68 X1 X0
       grind)
    | exact superpose eq68 eq484
    | (have j0 := eq484 (τ X1) (τ X0)
       grind)
    | exact resolve eq484 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq2944 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2918 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2918
    | (have j0 := eq2918 X0 X1
       grind)
    | exact resolve eq2918 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2918
  have eq2950 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2908 X0
       have j1 := eq2793 X0
       grind)
    | (have r₁ := eq2908 X0
       have r₂ := eq2793 X0
       grind)
    | exact resolve eq2908 eq2793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2793 eq2908
  have eq2953 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2944 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq2944
    | (have j0 := eq2944 X0 X1
       grind)
    | exact resolve eq2944 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2944
  have eq2955 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2953 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2953
    | (have j0 := eq2953 X0 X1
       grind)
    | exact resolve eq2953 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2953
  have eq2956 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2955 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2955
    | (have j0 := eq2955 X0 X1
       grind)
    | exact resolve eq2955 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2955
  have eq3340 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (M.op (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq2869 X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))
       have i₂ := eq667 X0
       grind)
    | exact superpose eq667 eq2869
    | (have j0 := eq2869 X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))
       grind)
    | exact resolve eq2869 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3341 : ∀ X0 : G, (M.op X0 X0) = (M.op (τ (M.op (σ X0) (σ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2869 X0 (τ (M.op (σ X0) (σ X0)))
       have i₂ := eq609 X0
       grind)
    | exact superpose eq609 eq2869
    | (have j0 := eq2869 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact resolve eq2869 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3342 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (M.op (τ (τ (M.op (σ (σ X0)) (σ (σ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq2869 X0 (τ (τ (M.op (σ (σ X0)) (σ (σ X0)))))
       have i₂ := eq741 X0
       grind)
    | exact superpose eq741 eq2869
    | (have j0 := eq2869 X0 (τ (τ (M.op (σ (σ X0)) (σ (σ X0)))))
       grind)
    | exact resolve eq2869 eq741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3526 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq2956 X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))
       have i₂ := eq667 X0
       grind)
    | exact superpose eq667 eq2956
    | (have j0 := eq2956 X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))
       grind)
    | exact resolve eq2956 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq3527 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq2956 X0 (τ (M.op (σ X0) (σ X0)))
       have i₂ := eq609 X0
       grind)
    | exact superpose eq609 eq2956
    | (have j0 := eq2956 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact resolve eq2956 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3528 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op (τ (τ (M.op (σ (σ X0)) (σ (σ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq2956 X0 (τ (τ (M.op (σ (σ X0)) (σ (σ X0)))))
       have i₂ := eq741 X0
       grind)
    | exact superpose eq741 eq2956
    | (have j0 := eq2956 X0 (τ (τ (M.op (σ (σ X0)) (σ (σ X0)))))
       grind)
    | exact resolve eq2956 eq741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq3537 : ∀ X0 : G, (M.op X0 X0) = (M.op (τ (τ (M.op (σ (σ X0)) (σ (σ X0))))) X0) := by
    intro X0
    first
    | (have j0 := eq3528 X0
       have j1 := eq3342 X0
       grind)
    | (have r₁ := eq3528 X0
       have r₂ := eq3342 X0
       grind)
    | exact resolve eq3528 eq3342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3342 eq3528
  have eq3538 : ∀ X0 : G, (M.op X0 X0) = (M.op (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have j0 := eq3527 X0
       have j1 := eq3341 X0
       grind)
    | (have r₁ := eq3527 X0
       have r₂ := eq3341 X0
       grind)
    | exact resolve eq3527 eq3341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3341 eq3527
  have eq3539 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) := by
    intro X0
    first
    | (have j0 := eq3526 X0
       have j1 := eq3340 X0
       grind)
    | (have r₁ := eq3526 X0
       have r₂ := eq3340 X0
       grind)
    | exact resolve eq3526 eq3340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3340 eq3526
  have eq3698 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq3538 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3538
    | exact resolve eq3538 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3538
  have eq5328 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq1245
       have i₂ := eq969 x y
       grind)
    | exact superpose eq969 eq1245
    | (have j1 := eq969 x y
       grind)
    | (have r₁ := eq1245
       have r₂ := eq969 x y
       grind)
    | exact resolve eq1245 eq969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969 eq1245
  have eq5329 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by grind
  clear eq5328
  have eq5495 : (M.op x y) = (τ (σ y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq5329
       grind)
    | exact superpose eq5329 eq9
    | exact resolve eq9 eq5329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5329
  have eq5547 : y = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq5495
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq5495
    | exact resolve eq5495 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5495
  have eq5548 : y = (k y x) := by
    first
    | (have j1 := eq85 y x
       grind)
    | (have r₁ := eq5547
       have r₂ := eq85 y x
       grind)
    | exact resolve eq5547 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq5547
  have eq5651 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq437 y x
       have i₂ := eq5548
       grind)
    | exact superpose eq5548 eq437
    | (have j0 := eq437 y x
       grind)
    | exact resolve eq437 eq5548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq5653 : y = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq2869 y x
       have i₂ := eq5548
       grind)
    | exact superpose eq5548 eq2869
    | (have j0 := eq2869 y x
       grind)
    | exact resolve eq2869 eq5548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2869
  have eq5654 : y ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq2956 y x
       have i₂ := eq5548
       grind)
    | exact superpose eq5548 eq2956
    | (have j0 := eq2956 y x
       grind)
    | exact resolve eq2956 eq5548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2956
  have eq5655 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq5653
       have r₂ := eq5654
       grind)
    | exact resolve eq5653 eq5654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5653 eq5654
  have eq5749 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq2950 y
       have i₂ := eq5655
       grind)
    | exact superpose eq5655 eq2950
    | exact resolve eq2950 eq5655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2950
  have eq6502 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (k (M.op X0 (M.op X0 X0)) X1) ∨ (M.op X1 (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op X0 X0)) X1) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2735 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq169 X0 X0 X0
       grind)
    | exact superpose eq169 eq2735
    | (have j0 := eq2735 (M.op X0 (M.op X0 X0)) X1
       have j1 := eq169 X0 X0 x
       grind)
    | (have r₁ := eq2735 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq169 X0 (M.op X0 X0) x
       grind)
    | exact resolve eq2735 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169 eq2735
  have eq6557 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op X0 X0)) X1) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0 X1
    first
    | (have j0 := eq6502 X0 X1
       have j1 := eq47 (M.op X0 (M.op X0 X0)) X1
       grind)
    | (have r₁ := eq6502 X0 X1
       have r₂ := eq47 (M.op X0 (M.op X0 X0)) X1
       grind)
    | exact resolve eq6502 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq6502
  have eq6570 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6557 X0 X1
       have i₂ := eq22 X0 X0
       grind)
    | exact superpose eq22 eq6557
    | (have j0 := eq6557 X0 X1
       grind)
    | exact resolve eq6557 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6557
  have eq6576 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6570 X0 X1
       have i₂ := eq22 X0 X0
       grind)
    | exact superpose eq22 eq6570
    | (have j0 := eq6570 X0 X1
       grind)
    | exact resolve eq6570 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6570
  have eq10892 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (k (M.op X1 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq6576 X1 (σ X0)
       grind)
    | exact superpose eq6576 eq20
    | (have j1 := eq6576 X1 X1
       grind)
    | exact resolve eq20 eq6576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq10896 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k (M.op X1 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq6576 X1 (τ X0)
       grind)
    | exact superpose eq6576 eq16
    | (have j1 := eq6576 X1 X1
       grind)
    | exact resolve eq16 eq6576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq6576
  have eq29093 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1253 (τ X1) (τ X0)
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq1253
    | exact resolve eq1253 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29273 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29093 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq29093
    | (have j0 := eq29093 X0 X1
       grind)
    | exact resolve eq29093 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29093
  have eq29294 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29273 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29273
    | (have j0 := eq29273 X0 X1
       grind)
    | exact resolve eq29273 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29273
  have eq29297 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (M.op X0 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29294 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq29294
    | (have j0 := eq29294 X0 X1
       grind)
    | exact resolve eq29294 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29294
  have eq29298 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29297 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29297
    | (have j0 := eq29297 X0 X1
       grind)
    | exact resolve eq29297 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29297
  have eq29873 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ (k X0 X1))) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29298 (τ X1) (τ X0)
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq29298
    | exact resolve eq29298 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq29298
  have eq45844 : ∀ X0 : G, (k (τ X0) (σ (M.op (τ (τ X0)) (τ (τ X0))))) = (τ (M.op X0 X0)) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10892 (σ (M.op (τ (τ X0)) (τ (τ X0)))) X0
       have i₂ := eq3539 X0
       grind)
    | exact superpose eq3539 eq10892
    | (have j0 := eq10892 X0 X0
       grind)
    | exact resolve eq10892 eq3539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3539 eq10892
  have eq45942 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq45844 X0
       have i₂ := eq608 (τ X0)
       grind)
    | exact superpose eq608 eq45844
    | (have j0 := eq45844 X0
       grind)
    | exact resolve eq45844 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608 eq45844
  have eq46320 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq29873 (M.op X0 X0) X0
       have i₂ := eq45942 X0
       grind)
    | exact superpose eq45942 eq29873
    | (have j1 := eq45942 X0
       grind)
    | exact resolve eq29873 eq45942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29873 eq45942
  have eq46334 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq46320 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46320
  have eq46344 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46334 X0
       have i₂ := eq3698 X0
       grind)
    | exact superpose eq3698 eq46334
    | (have j0 := eq46334 X0
       grind)
    | exact resolve eq46334 eq3698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3698 eq46334
  have eq48740 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (τ (M.op (σ (σ X0)) (σ (σ X0))))) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10896 (τ (M.op (σ (σ X0)) (σ (σ X0)))) X0
       have i₂ := eq3537 X0
       grind)
    | exact superpose eq3537 eq10896
    | (have j0 := eq10896 X0 X0
       grind)
    | exact resolve eq10896 eq3537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3537 eq10896
  have eq48854 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq48740 X0
       have i₂ := eq609 (σ X0)
       grind)
    | exact superpose eq609 eq48740
    | (have j0 := eq48740 X0
       grind)
    | exact resolve eq48740 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609 eq48740
  have eq49020 : y = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq48854 y
       have i₂ := eq5655
       grind)
    | exact superpose eq5655 eq48854
    | exact resolve eq48854 eq5655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48854
  have eq50086 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1253 (M.op x y) y
       have i₂ := eq49020
       grind)
    | exact superpose eq49020 eq1253
    | exact resolve eq1253 eq49020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253 eq49020
  have eq50096 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq50086
  have eq50101 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq50096
       have i₂ := eq5749
       grind)
    | exact superpose eq5749 eq50096
    | exact resolve eq50096 eq5749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50096
  have eq58758 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq46344 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq46344
    | exact resolve eq46344 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46344
  have eq77130 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ X0))
       have i₂ := eq58758 X0
       grind)
    | exact superpose eq58758 eq10
    | (have j1 := eq58758 X0
       grind)
    | exact resolve eq10 eq58758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58758
  have eq77565 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ X0))
       have i₂ := eq77130 X0
       grind)
    | exact superpose eq77130 eq10
    | (have j1 := eq77130 X0
       grind)
    | exact resolve eq10 eq77130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77130
  have eq77895 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0) (σ X0)
       have i₂ := eq77565 X0
       grind)
    | exact superpose eq77565 eq22
    | (have j1 := eq77565 X0
       grind)
    | exact resolve eq22 eq77565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77565
  have eq80720 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq77895 y
       have i₂ := eq5655
       grind)
    | exact superpose eq5655 eq77895
    | (have j0 := eq77895 y
       grind)
    | exact resolve eq77895 eq5655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5655 eq77895
  have eq80928 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq22 (σ y) (σ (M.op x y))
       have i₂ := eq80720
       grind)
    | exact superpose eq80720 eq22
    | exact resolve eq22 eq80720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq80720
  have eq80946 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq80928
       have i₂ := eq5749
       grind)
    | exact superpose eq5749 eq80928
    | exact resolve eq80928 eq5749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5749 eq80928
  have eq83053 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq5651
       have i₂ := eq50101
       grind)
    | exact superpose eq50101 eq5651
    | exact resolve eq5651 eq50101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50101
  have eq83061 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq80946
       have i₂ := eq5651
       grind)
    | exact superpose eq5651 eq80946
    | exact resolve eq80946 eq5651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80946
  have eq83109 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5651
  have eq83112 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq83053
  have eq83130 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq83061
       have r₂ := eq83109
       grind)
    | exact resolve eq83061 eq83109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83061 eq83109
  have eq83138 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq83112
       have r₂ := eq14
       grind)
    | exact resolve eq83112 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83112
  have eq83151 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq83130
       have r₂ := eq14
       grind)
    | exact resolve eq83130 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83130
  have eq83170 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 (M.op x y) X0
       have i₂ := eq83138
       grind)
    | exact superpose eq83138 eq13
    | exact resolve eq13 eq83138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83190 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (σ (k (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq79 (M.op x y) x
       have i₂ := eq83138
       grind)
    | exact superpose eq83138 eq79
    | exact resolve eq79 eq83138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq83203 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ (σ (k (M.op x y) X0)) ∨ (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq485 X0 (M.op x y)
       have i₂ := eq83138
       grind)
    | exact superpose eq83138 eq485
    | exact resolve eq485 eq83138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq83315 : ∀ X0 : G, (σ y) ≠ (σ (k (M.op x y) X0)) ∨ (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq83203 X0
       have i₂ := eq83151
       grind)
    | exact superpose eq83151 eq83203
    | (have j0 := eq83203 X0
       grind)
    | exact resolve eq83203 eq83151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83151 eq83203
  have eq83337 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (σ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq83170 X0
       have i₂ := eq13 y X0
       grind)
    | exact superpose eq13 eq83170
    | exact resolve eq83170 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83170
  have eq83355 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq83315 X0
       have j1 := eq83190 X0
       grind)
    | (have r₁ := eq83315 X0
       have r₂ := eq83190 X0
       grind)
    | exact resolve eq83315 eq83190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83190 eq83315
  have eq83365 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq83355 X0
       have i₂ := eq83337 X0
       grind)
    | exact superpose eq83337 eq83355
    | exact resolve eq83355 eq83337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83337 eq83355
  have eq87688 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq83365 x
       grind)
    | exact superpose eq83365 eq14
    | exact resolve eq14 eq83365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83365
  have eq88175 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq87688
       have i₂ := eq5548
       grind)
    | exact superpose eq5548 eq87688
    | exact resolve eq87688 eq5548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5548 eq87688
  have eq88393 : False := by grind
  exact eq88393

/-- `Equation844`: `x = x ◇ ((y ◇ y) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_pxx_pyx_Equation844 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law844 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law844.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X0 X2))) = X0 := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq22 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1) X0 (M.op (M.op X0 X0) x)
       have i₂ := eq8 (M.op X0 X0) X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (k X0 X2) = (M.op X2 X0) := by
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
  have eq43 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) X1
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X1 X1
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq37 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq60 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 X1
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0) X1
       have i₂ := eq22 X0 X0
       grind)
    | exact superpose eq22 eq11
    | (have r₁ := eq11 (M.op X0 X0) X1
       have r₂ := eq22 X0 X0
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq89 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq46 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq46 eq13
    | (have j1 := eq46 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq100 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0)
       have i₂ := eq66 X0 (τ X1)
       grind)
    | exact superpose eq66 eq16
    | exact resolve eq16 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq43 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq734 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq790 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq734 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq734
    | (have j0 := eq734 X0 X1
       grind)
    | exact resolve eq734 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq1205 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X0) X1) ∨ (σ (k X0 X2)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq100 X1 X1
       have i₂ := eq790 X0 X1
       grind)
    | exact superpose eq790 eq100
    | (have j1 := eq790 X2 X0
       grind)
    | exact resolve eq100 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq790
  have eq1249 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq205 (M.op X0 X0)
       have i₂ := eq66 X0 (M.op X0 X0)
       grind)
    | exact superpose eq66 eq205
    | (have j0 := eq205 (M.op X0 X0)
       grind)
    | exact resolve eq205 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq1261 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq205 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq205
    | (have j0 := eq205 (τ X0)
       grind)
    | exact resolve eq205 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq205
  have eq1271 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1249 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249
  have eq1276 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1261 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1261
    | (have j0 := eq1261 X0
       grind)
    | exact resolve eq1261 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261
  have eq1285 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1276 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1276
    | (have j0 := eq1276 X0
       grind)
    | exact resolve eq1276 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276
  have eq1661 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq60 (σ (M.op X0 X0)) X1
       have i₂ := eq1271 X0
       grind)
    | exact superpose eq1271 eq60
    | exact resolve eq60 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271
  have eq1723 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq89 x y X0
       grind)
    | exact superpose eq89 eq14
    | (have j1 := eq89 X0 y X0
       grind)
    | exact resolve eq14 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq1785 : ∀ X0 : G, (σ y) = (k (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq1723 X0
       have j1 := eq1205 y X0 x
       grind)
    | (have r₁ := eq1723 X0
       have r₂ := eq1205 y x x
       grind)
    | exact resolve eq1723 eq1205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205 eq1723
  have eq1827 : ∀ X0 : G, (τ (σ y)) = (k (τ (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq20 (σ y) X0
       have i₂ := eq1785 (σ X0)
       grind)
    | exact superpose eq1785 eq20
    | exact resolve eq20 eq1785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1785
  have eq1831 : ∀ X0 : G, y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq1827 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1827
    | exact resolve eq1827 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1827
  have eq1952 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1285 y
       have i₂ := eq1831 y
       grind)
    | exact superpose eq1831 eq1285
    | (have j0 := eq1285 y
       grind)
    | (have r₁ := eq1285 y
       have r₂ := eq1831 y
       grind)
    | exact resolve eq1285 eq1831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285 eq1831
  have eq1970 : y = (M.op y y) := by grind
  clear eq1952
  have eq2066 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq60 y X0
       have i₂ := eq1970
       grind)
    | exact superpose eq1970 eq60
    | exact resolve eq60 eq1970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq2822 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1661 y X0
       have i₂ := eq1970
       grind)
    | exact superpose eq1970 eq1661
    | exact resolve eq1661 eq1970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1661 eq1970
  have eq3020 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2822 (σ x)
       grind)
    | exact superpose eq2822 eq14
    | exact resolve eq14 eq2822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2822
  have eq3035 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq3020
       have i₂ := eq2066 x
       grind)
    | exact superpose eq2066 eq3020
    | exact resolve eq3020 eq2066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2066 eq3020
  have eq3036 : False := by grind
  exact eq3036

/-- `Equation844`: `x = x ◇ ((y ◇ y) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pxx_pxy_Equation844 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law844 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law844.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X0 X2))) = X0 := by
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
  have eq22 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1) X0 (M.op (M.op X0 X0) x)
       have i₂ := eq8 (M.op X0 X0) X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
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
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq44 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
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
  have eq46 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq37 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq60 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 X1
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq109 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq273 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 (σ X0) X1
       have i₂ := eq43 X2 X0
       grind)
    | exact superpose eq43 eq60
    | (have j1 := eq43 X2 X0
       grind)
    | exact resolve eq60 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq413 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq109 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq433 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq413 (σ X0)
       grind)
    | exact superpose eq413 eq13
    | exact resolve eq13 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq435 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq47 X0 X0
       have i₂ := eq413 (τ X0)
       grind)
    | exact superpose eq413 eq47
    | exact resolve eq47 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq445 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq435 X0
       have i₂ := eq413 X0
       grind)
    | exact superpose eq413 eq435
    | exact resolve eq435 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq447 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq433 X0
       have i₂ := eq413 X0
       grind)
    | exact superpose eq413 eq433
    | exact resolve eq433 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413 eq433
  have eq631 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq60 (τ X0) X1
       have i₂ := eq445 X0
       grind)
    | exact superpose eq445 eq60
    | exact resolve eq60 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq924 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq60 (σ X0) X1
       have i₂ := eq447 X0
       grind)
    | exact superpose eq447 eq60
    | exact resolve eq60 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq447
  have eq947 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq44 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq44
    | (have j0 := eq44 X0 X1
       grind)
    | exact resolve eq44 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq1028 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq947 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq947
    | (have j0 := eq947 X0 X1
       grind)
    | exact resolve eq947 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq30026 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq924 X0 X1
       have i₂ := eq1028 X2 X0
       grind)
    | exact superpose eq1028 eq924
    | (have j1 := eq1028 X2 X0
       grind)
    | exact resolve eq924 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924 eq1028
  have eq41505 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq273 y X0 x
       grind)
    | exact superpose eq273 eq14
    | (have j1 := eq273 y X0 x
       grind)
    | exact resolve eq14 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq41798 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq41505 X0
       have j1 := eq30026 y X0 x
       grind)
    | (have r₁ := eq41505 X0
       have r₂ := eq30026 y x x
       grind)
    | exact resolve eq41505 eq30026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30026 eq41505
  have eq42027 : ∀ X0 : G, (M.op X0 (τ (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq631 (σ y) X0
       have i₂ := eq41798 (σ y)
       grind)
    | exact superpose eq41798 eq631
    | exact resolve eq631 eq41798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq42093 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq41798 (σ x)
       grind)
    | exact superpose eq41798 eq14
    | exact resolve eq14 eq41798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41798
  have eq42150 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq42027 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq42027
    | exact resolve eq42027 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42027
  have eq43472 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq42093
       have i₂ := eq42150 x
       grind)
    | exact superpose eq42150 eq42093
    | exact resolve eq42093 eq42150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42093 eq42150
  have eq43473 : False := by grind
  exact eq43473

/-- `Equation844`: `x = x ◇ ((y ◇ y) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pyy_pxy_Equation844 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law844 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law844.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X0 X2))) = X0 := by
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
  have eq22 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1) X0 (M.op (M.op X0 X0) x)
       have i₂ := eq8 (M.op X0 X0) X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq37 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
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
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq44 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
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
  have eq46 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq37 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq60 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 X1
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X0 X0)
       have i₂ := eq22 X0 X0
       grind)
    | exact superpose eq22 eq11
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq22 X0 X0
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq89 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq46 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq46 eq13
    | (have j1 := eq46 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq101 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (M.op X0 X0)
       have i₂ := eq66 X0 (τ X1)
       grind)
    | exact superpose eq66 eq15
    | exact resolve eq15 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq205 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq43 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq734 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq44 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq44
    | (have j0 := eq44 X0 X1
       grind)
    | exact resolve eq44 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq790 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq734 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq734
    | (have j0 := eq734 X0 X1
       grind)
    | exact resolve eq734 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq1205 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq101 X1 X1
       have i₂ := eq790 X0 X1
       grind)
    | exact superpose eq790 eq101
    | (have j1 := eq790 X2 X0
       grind)
    | exact resolve eq101 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq790
  have eq1248 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq205 (M.op X0 X0)
       have i₂ := eq66 X0 (M.op X0 X0)
       grind)
    | exact superpose eq66 eq205
    | (have j0 := eq205 (M.op X0 X0)
       grind)
    | exact resolve eq205 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq1261 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq205 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq205
    | (have j0 := eq205 (τ X0)
       grind)
    | exact resolve eq205 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq205
  have eq1272 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1248 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248
  have eq1276 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1261 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1261
    | (have j0 := eq1261 X0
       grind)
    | exact resolve eq1261 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261
  have eq1285 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1276 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1276
    | (have j0 := eq1276 X0
       grind)
    | exact resolve eq1276 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276
  have eq1661 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq60 (σ (M.op X0 X0)) X1
       have i₂ := eq1272 X0
       grind)
    | exact superpose eq1272 eq60
    | exact resolve eq60 eq1272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1272
  have eq1723 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq89 x y X0
       grind)
    | exact superpose eq89 eq14
    | (have j1 := eq89 X0 y X0
       grind)
    | exact resolve eq14 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq1785 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq1723 X0
       have j1 := eq1205 y X0 x
       grind)
    | (have r₁ := eq1723 X0
       have r₂ := eq1205 y x x
       grind)
    | exact resolve eq1723 eq1205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205 eq1723
  have eq1825 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq33 X0 (σ y)
       have i₂ := eq1785 (σ X0)
       grind)
    | exact superpose eq1785 eq33
    | exact resolve eq33 eq1785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq1785
  have eq1831 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq1825 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1825
    | exact resolve eq1825 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1825
  have eq1952 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1285 y
       have i₂ := eq1831 y
       grind)
    | exact superpose eq1831 eq1285
    | (have j0 := eq1285 y
       grind)
    | (have r₁ := eq1285 y
       have r₂ := eq1831 y
       grind)
    | exact resolve eq1285 eq1831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285 eq1831
  have eq1970 : y = (M.op y y) := by grind
  clear eq1952
  have eq2064 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq60 y X0
       have i₂ := eq1970
       grind)
    | exact superpose eq1970 eq60
    | exact resolve eq60 eq1970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq2812 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1661 y X0
       have i₂ := eq1970
       grind)
    | exact superpose eq1970 eq1661
    | exact resolve eq1661 eq1970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1661 eq1970
  have eq3010 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2812 (σ x)
       grind)
    | exact superpose eq2812 eq14
    | exact resolve eq14 eq2812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2812
  have eq3025 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq3010
       have i₂ := eq2064 x
       grind)
    | exact superpose eq2064 eq3010
    | exact resolve eq3010 eq2064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2064 eq3010
  have eq3026 : False := by grind
  exact eq3026

/-- `Equation847`: `x = x ◇ ((y ◇ y) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pxx_pxy_Equation847 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law847 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law847.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X1 X2))) = X0 := by
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
  have eq22 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op (M.op x x) (M.op x x))
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X1 X1) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq22 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq22 eq11
    | (have j0 := eq11 X1 (M.op (M.op X0 X0) X0)
       grind)
    | (have r₁ := eq11 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq22 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq44 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq48 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
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
  have eq51 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq48 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq57 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq111 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 X0 X1 X2
       have i₂ := eq12 X3 X0
       grind)
    | exact superpose eq12 eq51
    | (have j0 := eq51 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | exact resolve eq51 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq187 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = (k X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq56 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq56 eq13
    | (have j1 := eq56 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X2 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq56 X1 X2 (τ X0)
       grind)
    | exact superpose eq56 eq15
    | (have j1 := eq56 X1 X2 X2
       grind)
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq218 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 X1) X1)) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X0
       have i₂ := eq37 X1 X0
       grind)
    | exact superpose eq37 eq12
    | (have j0 := eq12 X2 X0
       grind)
    | exact resolve eq12 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 (M.op (M.op X1 X1) X1)
       have i₂ := eq37 X1 (τ X0)
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq549 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X1) X1)) ≠ (k X0 (M.op (M.op X1 X1) X1)) ∨ (k X0 (M.op (M.op X1 X1) X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq194 X1 X1
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq194
    | exact resolve eq194 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq556 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq194 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq561 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X1) X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq549 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq684 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq556 (σ X0)
       grind)
    | exact superpose eq556 eq13
    | exact resolve eq13 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq684 X0
       have i₂ := eq556 X0
       grind)
    | exact superpose eq556 eq684
    | exact resolve eq684 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq838 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) X1
       have i₂ := eq691 X0
       grind)
    | exact superpose eq691 eq22
    | exact resolve eq22 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq968 : ∀ X0 X1 : G, (τ (k (σ X0) (M.op (M.op X1 X1) X1))) = (k X0 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 (σ X0)
       have i₂ := eq561 (σ X0) X1
       grind)
    | (have i₁ := eq44 X0 (M.op (M.op X1 X1) X1)
       have i₂ := eq561 (σ X0) X1
       grind)
    | exact superpose eq561 eq44
    | exact resolve eq44 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq973 : ∀ X0 X1 : G, (k X0 X0) = (τ (k (σ X0) (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq968 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq968
    | exact resolve eq968 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968
  have eq1004 : ∀ X0 X1 : G, (k X0 X0) = (k X0 (τ (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq973 X0 X1
       have i₂ := eq44 X0 (M.op (M.op X1 X1) X1)
       grind)
    | exact superpose eq44 eq973
    | exact resolve eq973 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973
  have eq1445 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op (M.op X0 X0) (M.op X0 X1))) (σ (M.op (M.op X0 X0) (M.op X0 X1))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq838 (M.op (M.op X0 X0) (M.op X0 X1)) X2
       have i₂ := eq8 (M.op (M.op X0 X0) (M.op X0 X1)) X0 X1
       grind)
    | exact superpose eq8 eq838
    | exact resolve eq838 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1446 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq838 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq22 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq22 eq838
    | exact resolve eq838 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq1537 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1446 X0 X1
       have i₂ := eq691 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq691 eq1446
    | exact resolve eq1446 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446
  have eq1538 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op (M.op (M.op X0 X0) (M.op X0 X1)) (M.op (M.op X0 X0) (M.op X0 X1))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1445 X0 X1 X2
       have i₂ := eq691 (M.op (M.op X0 X0) (M.op X0 X1))
       grind)
    | exact superpose eq691 eq1445
    | exact resolve eq1445 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445
  have eq1554 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 X0) X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1537 X0 X1
       have i₂ := eq22 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq22 eq1537
    | exact resolve eq1537 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1537
  have eq1555 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op (M.op X0 X0) (M.op X0 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1538 X0 X1 X2
       have i₂ := eq8 (M.op (M.op X0 X0) (M.op X0 X1)) X0 X1
       grind)
    | exact superpose eq8 eq1538
    | exact resolve eq1538 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538
  have eq1755 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) X0)) ≠ (σ (M.op (M.op X0 X0) X0)) ∨ (M.op X1 X1) = (k X1 (σ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ (M.op (M.op X0 X0) X0))
       have i₂ := eq1554 X0 (σ (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq1554 eq11
    | (have j0 := eq11 X1 (σ (M.op (M.op X0 X0) X0))
       grind)
    | (have r₁ := eq11 X0 (σ (M.op (M.op X0 X0) X0))
       have r₂ := eq1554 X0 (σ (M.op (M.op X0 X0) X0))
       grind)
    | exact resolve eq11 eq1554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554
  have eq1796 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have j0 := eq1755 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1755
  have eq2891 : ∀ X0 X1 : G, (τ (k X0 X0)) = (k (τ X0) (τ (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X0
       have i₂ := eq1004 (τ X0) X1
       grind)
    | (have i₁ := eq57 (M.op (M.op X1 X1) X1) X1
       have i₂ := eq1004 (τ X1) X1
       grind)
    | exact superpose eq1004 eq57
    | exact resolve eq57 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq2914 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (k X0 (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2891 X0 X1
       have i₂ := eq57 (M.op (M.op X1 X1) X1) X0
       grind)
    | exact superpose eq57 eq2891
    | exact resolve eq2891 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq2891
  have eq2975 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (k X0 (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2914 X0 X1
       have i₂ := eq556 X0
       grind)
    | exact superpose eq556 eq2914
    | exact resolve eq2914 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556 eq2914
  have eq6387 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X2 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq189 (σ X0) X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq189
    | (have j0 := eq189 X0 X1 X2
       grind)
    | exact resolve eq189 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq6713 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X2 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6387 X0 X1 X2
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq6387
    | (have j0 := eq6387 X0 X1 X2
       grind)
    | exact resolve eq6387 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6387
  have eq13598 : ∀ X0 X1 X2 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44 X0 (σ X1)
       have i₂ := eq187 X2 X1 (σ X0)
       grind)
    | exact superpose eq187 eq44
    | (have j1 := eq187 X2 X1 X2
       grind)
    | exact resolve eq44 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq187
  have eq13605 : ∀ X0 X1 X2 : G, (k X0 (τ (σ X1))) = (τ (σ (M.op X0 X0))) ∨ (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13598 X0 X1 X2
       have i₂ := eq691 X0
       grind)
    | exact superpose eq691 eq13598
    | (have j0 := eq13598 X0 X1 X2
       grind)
    | exact resolve eq13598 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13598
  have eq13771 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13605 X0 X1 X2
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq13605
    | (have j0 := eq13605 X0 X1 X2
       grind)
    | exact resolve eq13605 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13605
  have eq13813 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X0) ∨ (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13771 X0 X1 X2
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq13771
    | (have j0 := eq13771 X0 X1 X2
       grind)
    | exact resolve eq13771 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13771
  have eq19283 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X2 X1) = X2 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq111 X1 X2 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq19284 : ∀ X0 X1 X2 : G, (M.op X2 X1) = X2 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq19283 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19283
  have eq19641 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq19284 (τ X0) X1 X2
       grind)
    | exact superpose eq19284 eq15
    | (have j1 := eq19284 X0 X1 X2
       grind)
    | exact resolve eq15 eq19284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19284
  have eq201029 : ∀ X0 X2 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq2975 X0 x
       have i₂ := eq218 X0 x X2
       grind)
    | exact superpose eq218 eq2975
    | (have j1 := eq218 X0 x X2
       grind)
    | exact resolve eq2975 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq2975
  have eq201657 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq201029 (σ X0) X1
       have i₂ := eq691 X0
       grind)
    | exact superpose eq691 eq201029
    | (have j0 := eq201029 (σ X0) X1
       grind)
    | exact resolve eq201029 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201029
  have eq202272 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq201657 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq201657
    | (have j0 := eq201657 X0 X1
       grind)
    | exact resolve eq201657 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201657
  have eq202378 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq202272 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq202272
    | (have j0 := eq202272 X0 X1
       grind)
    | exact resolve eq202272 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202272
  have eq215658 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19641 (σ X0) X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq19641
    | (have j0 := eq19641 X0 X1 X2
       grind)
    | exact resolve eq19641 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19641
  have eq217007 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq215658 X0 X1 X2
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq215658
    | (have j0 := eq215658 X0 X1 X2
       grind)
    | exact resolve eq215658 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215658
  have eq268094 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq13813 X0 y x
       grind)
    | exact superpose eq13813 eq14
    | (have j1 := eq13813 X0 y x
       grind)
    | exact resolve eq14 eq13813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13813
  have eq268120 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq268094 X0
       have j1 := eq6713 X0 y X0
       grind)
    | (have r₁ := eq268094 X0
       have r₂ := eq6713 x y x
       grind)
    | exact resolve eq268094 eq6713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6713 eq268094
  have eq268426 : ∀ X0 X1 : G, (k X0 (σ (M.op (M.op X1 X1) X1))) = (k X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq1796 X1 X0
       have i₂ := eq268120 X0
       grind)
    | exact superpose eq268120 eq1796
    | exact resolve eq1796 eq268120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796
  have eq268681 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) y) := by
    intro X0
    first
    | (have i₁ := eq691 X0
       have i₂ := eq268120 (σ X0)
       grind)
    | exact superpose eq268120 eq691
    | exact resolve eq691 eq268120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq268697 : ∀ X0 X1 : G, (k X0 (σ (M.op (M.op X1 X1) X1))) = (σ (k (τ X0) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq232 X0 X1
       have i₂ := eq268120 (τ X0)
       grind)
    | exact superpose eq268120 eq232
    | exact resolve eq232 eq268120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq268761 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 y)) ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq217007 X0 y X1
       have i₂ := eq268120 X0
       grind)
    | exact superpose eq268120 eq217007
    | (have j0 := eq217007 X0 y X1
       grind)
    | exact resolve eq217007 eq268120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217007 eq268120
  have eq268777 : ∀ X0 X1 : G, (k X0 (σ (M.op (M.op X1 X1) X1))) = (k X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq268697 X0 X1
       have i₂ := eq15 X0 y
       grind)
    | exact superpose eq15 eq268697
    | exact resolve eq268697 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq268697
  have eq268891 : ∀ X0 : G, (k X0 (σ y)) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq268777 X0 x
       have i₂ := eq268426 X0 x
       grind)
    | exact superpose eq268426 eq268777
    | exact resolve eq268777 eq268426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268426 eq268777
  have eq269406 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq202378 y X0
       have i₂ := eq268891 X0
       grind)
    | exact superpose eq268891 eq202378
    | (have j0 := eq202378 y x
       grind)
    | exact resolve eq202378 eq268891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202378 eq268891
  have eq369436 : (σ (M.op x y)) ≠ (k (σ x) y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq269406 (σ x)
       grind)
    | exact superpose eq269406 eq14
    | exact resolve eq14 eq269406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269406
  have eq369471 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq369436
       have i₂ := eq268681 x
       grind)
    | exact superpose eq268681 eq369436
    | exact resolve eq369436 eq268681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268681 eq369436
  have eq369498 : y = (M.op y y) := by
    first
    | (have j1 := eq268761 x y
       grind)
    | (have r₁ := eq369471
       have r₂ := eq268761 x x
       grind)
    | exact resolve eq369471 eq268761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268761 eq369471
  have eq369845 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 y y
       have i₂ := eq369498
       grind)
    | exact superpose eq369498 eq8
    | exact resolve eq8 eq369498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369888 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1555 y y x
       have i₂ := eq369498
       grind)
    | exact superpose eq369498 eq1555
    | exact resolve eq1555 eq369498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1555
  have eq369976 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq369888 X0
       have i₂ := eq369498
       grind)
    | exact superpose eq369498 eq369888
    | exact resolve eq369888 eq369498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369888
  have eq370005 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq369845 X0
       have i₂ := eq369498
       grind)
    | exact superpose eq369498 eq369845
    | exact resolve eq369845 eq369498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369498 eq369845
  have eq372493 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq369976 (σ x)
       grind)
    | exact superpose eq369976 eq14
    | exact resolve eq14 eq369976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369976
  have eq372628 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq372493
       have i₂ := eq370005 x
       grind)
    | exact superpose eq370005 eq372493
    | exact resolve eq372493 eq370005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370005 eq372493
  have eq372629 : False := by grind
  exact eq372629

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation854 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law854 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
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
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq94 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq98 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq94 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq94 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq94 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq94 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq114 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq98 (σ X0) (σ X1)
       grind)
    | exact superpose eq98 eq13
    | exact resolve eq13 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq114 X0 X1
       have i₂ := eq98 X0 X1
       grind)
    | exact superpose eq98 eq114
    | exact resolve eq114 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq114
  have eq1334 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq121 x y
       grind)
    | exact superpose eq121 eq14
    | (have r₁ := eq14
       have r₂ := eq121 x y
       grind)
    | exact resolve eq14 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq1367 : False := by grind
  exact eq1367

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pyx_x_pyx_Equation854 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law854 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
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
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))) X0)) = X0 := by
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
  have eq44 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 X2))) = X1 ∨ (M.op X0 (M.op X1 X2)) = (k (M.op X1 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X1 X2
       have i₂ := eq12 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 (M.op X0 X2) (M.op X1 X2)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 (M.op X1 X2) X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq52 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq54 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq52
    | exact resolve eq52 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq52 X1 (τ X0)
       grind)
    | exact superpose eq52 eq16
    | (have j1 := eq52 X1 (τ X0)
       grind)
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq21 X0 X0 x x
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq21
    | exact resolve eq21 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X1 (M.op X0 (M.op X2 (M.op X0 X0)))))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X2 X1 X0 (M.op X0 X0)
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq21
    | exact resolve eq21 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op X0 X0)
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq8
    | exact resolve eq8 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 (M.op X0 X1) X0 X1
       have i₂ := eq99 (M.op X0 X1)
       grind)
    | exact superpose eq99 eq22
    | exact resolve eq22 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq142 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X0 X2) X0)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X0 (M.op (M.op X0 X2) X0)
       have i₂ := eq126 X0 X2
       grind)
    | exact superpose eq126 eq8
    | exact resolve eq8 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq298 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq44 X0 X0 X0
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq44
    | exact resolve eq44 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq310 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X1 (M.op X0 (M.op X2 (M.op X3 (M.op X0 X4))))))) = X1 ∨ (M.op X3 (M.op X0 X4)) = (k (M.op X0 X4) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq21 X2 X1 X0 (M.op X3 (M.op X0 X4))
       have i₂ := eq44 X3 X0 X4
       grind)
    | exact superpose eq44 eq21
    | (have j1 := eq44 X2 X1 (M.op X0 (M.op X2 (M.op X3 (M.op X0 X4))))
       grind)
    | exact resolve eq21 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq330 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq110 X0 (M.op X1 X0)
       have i₂ := eq8 X0 X1 X0
       grind)
    | exact superpose eq8 eq110
    | exact resolve eq110 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq536 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X1)
       have i₂ := eq330 X1 X0
       grind)
    | exact superpose eq330 eq11
    | (have j0 := eq11 X1 X0
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq330 X0 X0
       grind)
    | exact resolve eq11 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq578 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (k X0 X1)) (M.op X2 (σ X0)))) = X2 ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (σ X1) (σ X0)
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq8
    | (have j1 := eq49 X1 X0
       grind)
    | exact resolve eq8 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq639 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1135 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq70 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq70
    | exact resolve eq70 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq1194 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1135 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1135
    | (have j0 := eq1135 X0 X1
       grind)
    | exact resolve eq1135 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq1215 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq65 y x
       grind)
    | exact superpose eq65 eq14
    | (have j1 := eq65 y x
       grind)
    | exact resolve eq14 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq1365 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq536 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq536 X1 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq536
    | (have j0 := eq536 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq536 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq536 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq536 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1380 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq536 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq1384 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1365 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1365
  have eq1559 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq1380 (σ X0)
       grind)
    | exact superpose eq1380 eq28
    | exact resolve eq28 eq1380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1560 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq15 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq1380 (τ X0)
       grind)
    | exact superpose eq1380 eq15
    | exact resolve eq15 eq1380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq1380
  have eq1561 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1560 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1560
    | exact resolve eq1560 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1560
  have eq1562 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1559 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1559
    | exact resolve eq1559 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1559
  have eq2504 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1384 X0 (M.op X0 X0)
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq1384
    | exact resolve eq1384 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384
  have eq3250 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq639 (τ X1) (τ X0)
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq639
    | (have j0 := eq639 (τ X1) (τ X0)
       grind)
    | exact resolve eq639 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq3276 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3250 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3250
    | (have j0 := eq3250 X0 X1
       grind)
    | exact resolve eq3250 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3250
  have eq3281 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3276 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq3276
    | (have j0 := eq3276 X0 X1
       grind)
    | exact resolve eq3276 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3276
  have eq3282 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3281 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3281
    | (have j0 := eq3281 X0 X1
       grind)
    | exact resolve eq3281 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3281
  have eq3283 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3282 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3282
    | (have j0 := eq3282 X0 X1
       grind)
    | exact resolve eq3282 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3282
  have eq3298 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq3283 X0 (σ (M.op (τ X0) (τ X0)))
       have i₂ := eq1561 X0
       grind)
    | exact superpose eq1561 eq3283
    | (have j0 := eq3283 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | exact resolve eq3283 eq1561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3300 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq3283 X0 (τ (M.op (σ X0) (σ X0)))
       have i₂ := eq1562 X0
       grind)
    | exact superpose eq1562 eq3283
    | (have j0 := eq3283 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact resolve eq3283 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7251 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq1215
       have i₂ := eq1194 x y
       grind)
    | exact superpose eq1194 eq1215
    | (have j1 := eq1194 x y
       grind)
    | (have r₁ := eq1215
       have r₂ := eq1194 x y
       grind)
    | exact resolve eq1215 eq1194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194 eq1215
  have eq7252 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by grind
  clear eq7251
  have eq7497 : (M.op x y) = (τ (σ y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq7252
       grind)
    | exact superpose eq7252 eq9
    | exact resolve eq9 eq7252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7252
  have eq7541 : y = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq7497
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq7497
    | exact resolve eq7497 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7497
  have eq7542 : y = (k y x) := by
    first
    | (have j1 := eq71 y x
       grind)
    | (have r₁ := eq7541
       have r₂ := eq71 y x
       grind)
    | exact resolve eq7541 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq7541
  have eq7847 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq7542
       grind)
    | exact superpose eq7542 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq7542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7851 : y ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq3283 y x
       have i₂ := eq7542
       grind)
    | exact superpose eq7542 eq3283
    | (have j0 := eq3283 y x
       grind)
    | exact resolve eq3283 eq7542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3283
  have eq7869 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (τ (k X0 X1))) (M.op X2 (σ (τ X0))))) = X2 ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq578 (τ X0) (τ X1) X2
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq578
    | (have j0 := eq578 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq578 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq7872 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op X0 (σ y)))) = X0 ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq578 y x X0
       have i₂ := eq7542
       grind)
    | exact superpose eq7542 eq578
    | (have j0 := eq578 y x x
       grind)
    | exact resolve eq578 eq7542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq7987 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (τ (k X0 X1))) (M.op X2 X0))) = X2 ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7869 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7869
    | (have j0 := eq7869 X0 X1 X2
       grind)
    | exact resolve eq7869 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7869
  have eq7991 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (k X0 X1) (M.op X2 X0))) = X2 ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7987 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq7987
    | (have j0 := eq7987 X0 X1 X2
       grind)
    | exact resolve eq7987 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7987
  have eq7992 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (σ (τ X1)) X0) ∨ (M.op X2 (M.op (k X0 X1) (M.op X2 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7991 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7991
    | (have j0 := eq7991 X0 X1 X2
       grind)
    | exact resolve eq7991 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7991
  have eq7993 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (k X0 X1) (M.op X2 X0))) = X2 ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7992 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq7992
    | (have j0 := eq7992 X0 X1 X2
       grind)
    | exact resolve eq7992 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7992
  have eq17922 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X1 (M.op (M.op X3 X4) (M.op X2 X0))))) = X1 ∨ (k (M.op (M.op X3 X4) (M.op X0 X4)) X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq310 (M.op X1 X2) X1 X2 X0 (M.op X0 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq310
    | exact resolve eq310 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq30176 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2504 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2504
  have eq30182 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq30176 X0
       have j1 := eq298 X0
       grind)
    | (have r₁ := eq30176 X0
       have r₂ := eq298 X0
       grind)
    | exact resolve eq30176 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298 eq30176
  have eq30536 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq20 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq30182 (σ X0)
       grind)
    | exact superpose eq30182 eq20
    | exact resolve eq20 eq30182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq30541 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq30182 (τ X0)
       grind)
    | exact superpose eq30182 eq16
    | exact resolve eq16 eq30182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq30182
  have eq30546 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq30541 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30541
    | exact resolve eq30541 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30541
  have eq30550 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq30536 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq30536
    | exact resolve eq30536 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30536
  have eq31706 : ∀ X0 : G, (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 (σ (M.op (τ X0) (τ X0))) X0
       have i₂ := eq30546 X0
       grind)
    | exact superpose eq30546 eq52
    | exact resolve eq52 eq30546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30546
  have eq32176 : ∀ X0 : G, (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 (τ (M.op (σ X0) (σ X0))) X0
       have i₂ := eq30550 X0
       grind)
    | exact superpose eq30550 eq52
    | exact resolve eq52 eq30550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq30550
  have eq112241 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq110 X0 (k X0 X1)
       have i₂ := eq7993 X0 X1 X0
       grind)
    | exact superpose eq7993 eq110
    | (have j1 := eq7993 X0 X1 x
       grind)
    | exact resolve eq110 eq7993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7993
  have eq112377 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (M.op (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq112241 X0 (σ (M.op (τ X0) (τ X0)))
       have i₂ := eq1561 X0
       grind)
    | exact superpose eq1561 eq112241
    | (have j0 := eq112241 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | exact resolve eq112241 eq1561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1561
  have eq112378 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (M.op (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq112241 X0 (τ (M.op (σ X0) (σ X0)))
       have i₂ := eq1562 X0
       grind)
    | exact superpose eq1562 eq112241
    | (have j0 := eq112241 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact resolve eq112241 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1562
  have eq112407 : y = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq112241 y x
       have i₂ := eq7542
       grind)
    | exact superpose eq7542 eq112241
    | (have j0 := eq112241 y x
       grind)
    | exact resolve eq112241 eq7542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112241
  have eq112505 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq112407
       have r₂ := eq7851
       grind)
    | exact resolve eq112407 eq7851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7851 eq112407
  have eq112507 : ∀ X0 : G, (M.op X0 X0) = (M.op (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have j0 := eq112378 X0
       have j1 := eq3300 X0
       grind)
    | (have r₁ := eq112378 X0
       have r₂ := eq3300 X0
       grind)
    | exact resolve eq112378 eq3300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3300 eq112378
  have eq112508 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have j0 := eq112377 X0
       have j1 := eq3298 X0
       grind)
    | (have r₁ := eq112377 X0
       have r₂ := eq3298 X0
       grind)
    | exact resolve eq112377 eq3298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3298 eq112377
  have eq114356 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq112507 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq112507
    | exact resolve eq112507 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112507
  have eq114614 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq112508 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq112508
    | exact resolve eq112508 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114749 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) (M.op X1 (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq108 X0 X1 (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))))
       have i₂ := eq112508 (M.op X0 X0)
       grind)
    | exact superpose eq112508 eq108
    | exact resolve eq108 eq112508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq112508
  have eq114793 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) (M.op X1 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq114749 X0 X1
       have i₂ := eq8 X0 X0 X0
       grind)
    | exact superpose eq8 eq114749
    | exact resolve eq114749 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114749
  have eq115180 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (M.op (M.op X1 (τ X0)) (M.op (τ X0) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (τ (M.op X0 X0)) X1 (τ X0)
       have i₂ := eq114356 X0
       grind)
    | exact superpose eq114356 eq8
    | exact resolve eq8 eq114356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115409 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq114614 y
       have i₂ := eq112505
       grind)
    | exact superpose eq112505 eq114614
    | exact resolve eq114614 eq112505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115441 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (M.op (M.op X1 (σ X0)) (M.op (σ X0) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ (M.op X0 X0)) X1 (σ X0)
       have i₂ := eq114614 X0
       grind)
    | exact superpose eq114614 eq8
    | exact resolve eq8 eq114614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134441 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) (M.op X0 X1)) X0) = X0 ∨ (M.op X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17922 X0 X0 (M.op X0 X1) X0 X1
       have i₂ := eq142 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq142 eq17922
    | (have j0 := eq17922 X0 X1 x X0 X1
       grind)
    | exact resolve eq17922 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq17922
  have eq146435 : ∀ X0 : G, (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) = (M.op (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) X0) := by
    intro X0
    first
    | (have i₁ := eq110 X0 (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))))
       have i₂ := eq114793 X0 X0
       grind)
    | exact superpose eq114793 eq110
    | exact resolve eq110 eq114793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147683 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31706 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq31706
    | exact resolve eq31706 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31706
  have eq148366 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32176 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq32176
    | exact resolve eq32176 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32176
  have eq247682 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq21 (τ X0) (τ (M.op X0 X0)) x (τ X0)
       have i₂ := eq115180 X0 x
       grind)
    | exact superpose eq115180 eq21
    | exact resolve eq21 eq115180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115180
  have eq247741 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq247682 X0
       have i₂ := eq148366 X0
       grind)
    | exact superpose eq148366 eq247682
    | (have j1 := eq148366 X0
       grind)
    | exact resolve eq247682 eq148366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148366 eq247682
  have eq247754 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq247741 X0
       have i₂ := eq114356 X0
       grind)
    | exact superpose eq114356 eq247741
    | (have j0 := eq247741 X0
       grind)
    | exact resolve eq247741 eq114356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114356 eq247741
  have eq247846 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq247754 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq247754
    | exact resolve eq247754 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247754
  have eq248261 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ X0))
       have i₂ := eq247846 X0
       grind)
    | exact superpose eq247846 eq10
    | (have j1 := eq247846 X0
       grind)
    | exact resolve eq10 eq247846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247846
  have eq248409 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ X0))
       have i₂ := eq248261 X0
       grind)
    | exact superpose eq248261 eq10
    | (have j1 := eq248261 X0
       grind)
    | exact resolve eq10 eq248261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248261
  have eq248561 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq248409 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248409
  have eq250370 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq21 (σ X0) (σ (M.op X0 X0)) x (σ X0)
       have i₂ := eq115441 X0 x
       grind)
    | exact superpose eq115441 eq21
    | exact resolve eq21 eq115441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq115441
  have eq250438 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq250370 y
       have i₂ := eq112505
       grind)
    | exact superpose eq112505 eq250370
    | exact resolve eq250370 eq112505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250444 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq250370 X0
       have i₂ := eq147683 X0
       grind)
    | exact superpose eq147683 eq250370
    | (have j1 := eq147683 X0
       grind)
    | exact resolve eq250370 eq147683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147683 eq250370
  have eq250457 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq250444 X0
       have i₂ := eq114614 X0
       grind)
    | exact superpose eq114614 eq250444
    | (have j0 := eq250444 X0
       grind)
    | exact resolve eq250444 eq114614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114614 eq250444
  have eq250537 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq250457 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq250457
    | exact resolve eq250457 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250457
  have eq251038 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = X0 ∨ (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op (τ X0) (τ X0))
       have i₂ := eq250537 X0
       grind)
    | exact superpose eq250537 eq9
    | (have j1 := eq250537 X0
       grind)
    | exact resolve eq9 eq250537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250537
  have eq251144 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op (τ X0) (τ X0))
       have i₂ := eq251038 X0
       grind)
    | exact superpose eq251038 eq9
    | (have j1 := eq251038 X0
       grind)
    | exact resolve eq9 eq251038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251038
  have eq251264 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq251144 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq251144
    | exact resolve eq251144 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251286 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq99 (τ X0)
       have i₂ := eq251144 X0
       grind)
    | exact superpose eq251144 eq99
    | (have j1 := eq251144 X0
       grind)
    | exact resolve eq99 eq251144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251144
  have eq251408 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ X0))
       have i₂ := eq251264 X0
       grind)
    | exact superpose eq251264 eq10
    | (have j1 := eq251264 X0
       grind)
    | exact resolve eq10 eq251264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251264
  have eq251560 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq99 (σ X0)
       have i₂ := eq251408 X0
       grind)
    | exact superpose eq251408 eq99
    | (have j1 := eq251408 X0
       grind)
    | exact resolve eq99 eq251408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq251408
  have eq251737 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq251560 y
       have i₂ := eq7847
       grind)
    | exact superpose eq7847 eq251560
    | exact resolve eq251560 eq7847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7847 eq251560
  have eq251771 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq251737
  have eq251797 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq250438
       have i₂ := eq251771
       grind)
    | exact superpose eq251771 eq250438
    | exact resolve eq250438 eq251771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250438 eq251771
  have eq251830 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq251797
       have i₂ := eq115409
       grind)
    | exact superpose eq115409 eq251797
    | exact resolve eq251797 eq115409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115409 eq251797
  have eq252048 : (τ y) = (M.op (τ y) (τ (M.op x y))) ∨ (τ y) = (M.op (τ y) (τ y)) := by
    first
    | (have i₁ := eq251286 y
       have i₂ := eq112505
       grind)
    | exact superpose eq112505 eq251286
    | (have j0 := eq251286 y
       grind)
    | exact resolve eq251286 eq112505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251286
  have eq325746 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq110 (σ y) (σ y)
       have i₂ := eq7872 (σ y)
       grind)
    | exact superpose eq7872 eq110
    | exact resolve eq110 eq7872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq7872
  have eq325754 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq325746
       have i₂ := eq251830
       grind)
    | exact superpose eq251830 eq325746
    | exact resolve eq325746 eq251830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251830 eq325746
  have eq325782 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq325754
       have r₂ := eq14
       grind)
    | exact resolve eq325754 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325754
  have eq325806 : (M.op x y) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq325782
       grind)
    | exact superpose eq325782 eq9
    | exact resolve eq9 eq325782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325782
  have eq325877 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq325806
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq325806
    | exact resolve eq325806 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325806
  have eq325878 : y = (M.op x y) := by grind
  clear eq325877
  have eq326029 : (τ y) = (M.op (τ y) (τ y)) ∨ (τ y) = (M.op (τ y) (τ y)) := by
    first
    | (have i₁ := eq252048
       have i₂ := eq325878
       grind)
    | exact superpose eq325878 eq252048
    | exact resolve eq252048 eq325878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252048
  have eq326455 : x = (M.op x (M.op (σ (M.op (τ (M.op y y)) (τ (M.op y y)))) y)) := by
    first
    | (have i₁ := eq114793 y x
       have i₂ := eq325878
       grind)
    | exact superpose eq325878 eq114793
    | exact resolve eq114793 eq325878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114793
  have eq326514 : x = (k (M.op y y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq134441 x y
       have i₂ := eq325878
       grind)
    | exact superpose eq325878 eq134441
    | exact resolve eq134441 eq325878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134441
  have eq326819 : (τ y) = (M.op (τ y) (τ y)) := by grind
  clear eq326029
  have eq326875 : x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq326514
       have i₂ := eq112505
       grind)
    | exact superpose eq112505 eq326514
    | exact resolve eq326514 eq112505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326514
  have eq326889 : x = (M.op x (σ (M.op (τ (M.op y y)) (τ (M.op y y))))) := by
    first
    | (have i₁ := eq326455
       have i₂ := eq146435 y
       grind)
    | exact superpose eq146435 eq326455
    | exact resolve eq326455 eq146435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146435 eq326455
  have eq327056 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq326875
       have i₂ := eq325878
       grind)
    | exact superpose eq325878 eq326875
    | exact resolve eq326875 eq325878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326875
  have eq327060 : x = (M.op x (σ (M.op (τ (M.op x y)) (τ (M.op x y))))) := by
    first
    | (have i₁ := eq326889
       have i₂ := eq112505
       grind)
    | exact superpose eq112505 eq326889
    | exact resolve eq326889 eq112505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112505 eq326889
  have eq327118 : x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq327056
       have i₂ := eq7542
       grind)
    | exact superpose eq7542 eq327056
    | exact resolve eq327056 eq7542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7542 eq327056
  have eq327119 : x = (M.op x (σ (M.op (τ y) (τ y)))) := by
    first
    | (have i₁ := eq327060
       have i₂ := eq325878
       grind)
    | exact superpose eq325878 eq327060
    | exact resolve eq327060 eq325878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327060
  have eq327138 : x = y ∨ x = y := by
    first
    | (have i₁ := eq327118
       have i₂ := eq325878
       grind)
    | exact superpose eq325878 eq327118
    | exact resolve eq327118 eq325878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325878 eq327118
  have eq327139 : x = y := by grind
  clear eq327138
  have eq327140 : x = (M.op x (σ (τ y))) := by
    first
    | (have i₁ := eq327119
       have i₂ := eq326819
       grind)
    | exact superpose eq326819 eq327119
    | exact resolve eq327119 eq326819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326819 eq327119
  have eq327150 : x = (M.op x y) := by
    first
    | (have i₁ := eq327140
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq327140
    | exact resolve eq327140 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327140
  have eq327156 : x = (M.op x x) := by
    first
    | (have i₁ := eq327150
       have i₂ := eq327139
       grind)
    | exact superpose eq327139 eq327150
    | exact resolve eq327150 eq327139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327150
  have eq327158 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq327139
       grind)
    | exact superpose eq327139 eq14
    | exact resolve eq14 eq327139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327139
  have eq327917 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq327158
       have i₂ := eq327156
       grind)
    | exact superpose eq327156 eq327158
    | exact resolve eq327158 eq327156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327158
  have eq329372 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq248561 x
       have i₂ := eq327156
       grind)
    | exact superpose eq327156 eq248561
    | (have j0 := eq248561 x
       grind)
    | exact resolve eq248561 eq327156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248561 eq327156
  have eq330032 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq329372
  have eq330114 : False := by grind
  exact eq330114
