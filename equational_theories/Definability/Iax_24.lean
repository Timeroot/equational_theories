import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4502`: `x ◇ (y ◇ y) = (z ◇ w) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_y_x_pxy_Equation4502 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4502 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4502.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
    intro X0 X1 X2 X3
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq17 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) (M.op X2 X2)) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq8 X3 (M.op X2 X2) X4 X5
       have i₂ := eq8 (M.op X2 X2) X2 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X4 X5) X2) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq8 x X2 X4 X5
       have i₂ := eq8 x X2 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x x
       have i₂ := eq8 X2 X1 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X2 X3) ∨ (k X1 (M.op X2 X3)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 X1 (M.op X2 X3)
       have i₂ := eq8 X0 X1 X2 X3
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 X1 (M.op X2 X3)
       grind)
    | (have r₁ := eq11 (M.op X1 X1) (M.op (M.op X2 X3) X1)
       have r₂ := eq8 (M.op (M.op X2 X3) X1) X1 X2 X3
       grind)
    | (have r₁ := eq11 X1 (M.op X0 (M.op X1 X1))
       have r₂ := eq8 X0 X1 X0 (M.op X1 X1)
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq31 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq32 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
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
  have eq39 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
    | (have i₁ := eq29 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq108 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X0 (M.op X1 X1))) = (M.op (M.op X3 X4) (M.op X1 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X2 (M.op X1 X1) X3 X4
       have i₂ := eq22 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq8 X2 (M.op X1 X1) X3 X4
       have i₂ := eq22 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 X1
       have i₂ := eq12 (σ X0) X1
       grind)
    | exact superpose eq12 eq39
    | (have j1 := eq12 (σ X0) X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 X6 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op X6 (M.op X3 X3)) := by
    intro X0 X1 X2 X3 X6
    first
    | (have i₁ := eq22 (M.op x x) X3 X6
       have i₂ := eq17 X1 X2 X3 X0 x x
       grind)
    | (have i₁ := eq22 X3 (M.op X0 X1) X2
       have i₂ := eq17 X0 X1 (M.op X0 X1) X3 x x
       grind)
    | exact superpose eq17 eq22
    | exact resolve eq22 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq22
  have eq586 : ∀ X0 X1 : G, (k X0 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq25 X0 X0 X1 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq602 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op X0 X1) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq586 X2 x
       have i₂ := eq8 x X2 X0 X1
       grind)
    | exact superpose eq8 eq586
    | exact resolve eq586 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq632 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X0
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq31
    | (have j0 := eq31 X1 X0
       have j1 := eq31 X1 X0
       grind)
    | exact resolve eq31 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq634 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq31 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq31 X0 X1
       grind)
    | exact resolve eq11 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq653 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq31 X1 X0
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq31 X0 X1
       grind)
    | exact resolve eq11 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq664 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq665 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq653 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq666 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq665 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq665
    | (have j0 := eq665 X0 X1
       grind)
    | exact resolve eq665 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq667 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq634 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq634
    | (have j0 := eq634 X0 X1
       grind)
    | exact resolve eq634 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq4170 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
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
  have eq4223 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4170 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq4170
    | (have j0 := eq4170 X0 X1
       grind)
    | exact resolve eq4170 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4170
  have eq6421 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq666 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq666
    | exact resolve eq666 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq6503 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6421 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6421
    | (have j0 := eq6421 X0 X1
       grind)
    | exact resolve eq6421 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6421
  have eq6505 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6503 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6503
    | (have j0 := eq6503 X0 X1
       grind)
    | exact resolve eq6503 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6503
  have eq17841 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6505 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6505
    | exact resolve eq6505 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6505
  have eq19062 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq17841 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17841
  have eq24857 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq667 (τ X0) (τ X1)
       have i₂ := eq68 X1 X0
       grind)
    | exact superpose eq68 eq667
    | (have j0 := eq667 (τ X0) (τ X1)
       grind)
    | exact resolve eq667 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq667
  have eq24894 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24857 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq24857
    | (have j0 := eq24857 X0 X1
       grind)
    | exact resolve eq24857 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24857
  have eq24906 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24894 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24894
    | (have j0 := eq24894 X0 X1
       grind)
    | exact resolve eq24894 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24894
  have eq24915 : ∀ X0 X1 : G, (σ (τ X1)) = (k (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24906 X0 X1
       have i₂ := eq16 X0 (τ X1)
       grind)
    | exact superpose eq16 eq24906
    | (have j0 := eq24906 X0 X1
       grind)
    | exact resolve eq24906 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24906
  have eq24924 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24915 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24915
    | (have j0 := eq24915 X0 X1
       grind)
    | exact resolve eq24915 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24915
  have eq24927 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24924 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24924
    | (have j0 := eq24924 X0 X1
       grind)
    | exact resolve eq24924 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24924
  have eq24928 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24927 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24927
    | (have j0 := eq24927 X0 X1
       grind)
    | exact resolve eq24927 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24927
  have eq24929 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq24928 X0 X1
       have j1 := eq19062 X1 X0
       grind)
    | (have r₁ := eq24928 X1 X0
       have r₂ := eq19062 X0 X1
       grind)
    | (have r₁ := eq24928 X0 X1
       have r₂ := eq19062 X0 X1
       grind)
    | exact resolve eq24928 eq19062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24928
  have eq24941 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (M.op X1 X2) X0) = (k (M.op (M.op X1 X2) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24929 X0 (M.op (M.op X1 X2) X0)
       have i₂ := eq602 X1 X2 X0
       grind)
    | exact superpose eq602 eq24929
    | (have j0 := eq24929 X0 (M.op (M.op X1 X2) X0)
       grind)
    | (have r₁ := eq24929 X2 (M.op (M.op X0 X1) X2)
       have r₂ := eq602 X0 X1 X2
       grind)
    | exact resolve eq24929 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602 eq24929
  have eq24983 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (k (M.op (M.op X1 X2) X0) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq24941 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24941
  have eq40888 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq632 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq632
    | exact resolve eq632 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq41087 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq40888 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq40888
    | (have j0 := eq40888 X0 X1
       grind)
    | exact resolve eq40888 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq40888
  have eq41091 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq41087 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq41087
    | (have j0 := eq41087 X0 X1
       grind)
    | exact resolve eq41087 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq41087
  have eq41093 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq41091 X0 X1
       have j1 := eq11 X0 (σ X1)
       grind)
    | (have r₁ := eq41091 X0 X1
       have r₂ := eq11 X0 (σ X1)
       grind)
    | exact resolve eq41091 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41091
  have eq41140 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 (σ X1)
       have i₂ := eq41093 (σ X0) X1
       grind)
    | exact superpose eq41093 eq39
    | (have j1 := eq41093 (σ X0) X1
       grind)
    | exact resolve eq39 eq41093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq41093
  have eq41214 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq41140 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq41140
    | (have j0 := eq41140 X0 X1
       grind)
    | exact resolve eq41140 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41140
  have eq41237 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq41214 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq41214
    | (have j0 := eq41214 X0 X1
       grind)
    | exact resolve eq41214 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41214
  have eq41245 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq41237 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq41237
    | (have j0 := eq41237 X0 X1
       grind)
    | exact resolve eq41237 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41237
  have eq46163 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq41245 y x
       grind)
    | exact superpose eq41245 eq14
    | (have j1 := eq41245 y x
       grind)
    | exact resolve eq14 eq41245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41245
  have eq46645 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq46163
       have i₂ := eq4223 x y
       grind)
    | exact superpose eq4223 eq46163
    | (have j1 := eq4223 x y
       grind)
    | (have r₁ := eq46163
       have r₂ := eq4223 x y
       grind)
    | exact resolve eq46163 eq4223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4223 eq46163
  have eq46646 : y = (k y x) ∨ y = (M.op y x) := by grind
  clear eq46645
  have eq46649 : y = (k y x) := by
    first
    | (have j1 := eq19062 y x
       grind)
    | (have r₁ := eq46646
       have r₂ := eq19062 y x
       grind)
    | exact resolve eq46646 eq19062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19062 eq46646
  have eq46819 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq46649
       grind)
    | exact superpose eq46649 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq46649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49714 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 y x
       have i₂ := eq46819
       grind)
    | exact superpose eq46819 eq8
    | exact resolve eq8 eq46819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49719 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 X1 X2 y x
       have i₂ := eq46819
       grind)
    | exact superpose eq46819 eq18
    | exact resolve eq18 eq46819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49746 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X1)) = (M.op X0 (M.op y X1)) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X0 y x X1 X2
       have i₂ := eq46819
       grind)
    | exact superpose eq46819 eq176
    | exact resolve eq176 eq46819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq49803 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq24983 X0 y x
       have i₂ := eq46819
       grind)
    | exact superpose eq46819 eq24983
    | exact resolve eq24983 eq46819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122884 : ∀ X0 X1 : G, (M.op y X1) = (M.op X0 (M.op y X1)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq49714 x X1
       have i₂ := eq49746 X0 X1 x
       grind)
    | (have i₁ := eq49714 X0 y
       have i₂ := eq49746 X0 y x
       grind)
    | exact superpose eq49746 eq49714
    | exact resolve eq49714 eq49746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49714 eq49746
  have eq123177 : ∀ X0 X1 : G, (M.op y X1) = (M.op X0 (M.op y X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq122884 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122884
  have eq123202 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq123177 X0 x
       have i₂ := eq46819
       grind)
    | exact superpose eq46819 eq123177
    | exact resolve eq123177 eq46819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46819
  have eq123645 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq123202 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123202
  have eq124117 : y = (k y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq49803 y
       have i₂ := eq123645 y
       grind)
    | exact superpose eq123645 eq49803
    | exact resolve eq49803 eq123645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49803
  have eq124230 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq124238 : y = (k y y) ∨ x = (M.op x y) := by grind
  clear eq124117
  have eq124302 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq664 y
       have i₂ := eq124238
       grind)
    | exact superpose eq124238 eq664
    | (have j0 := eq664 y
       grind)
    | exact resolve eq664 eq124238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124238
  have eq124326 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq124302
  have eq126098 : ∀ X0 : G, (M.op (σ y) X0) = (M.op y X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq49719 (σ y) (σ y) X0
       have i₂ := eq124326
       grind)
    | exact superpose eq124326 eq49719
    | exact resolve eq49719 eq124326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49719
  have eq126103 : ∀ X0 : G, (M.op (σ y) X0) = (M.op y X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq126098 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126098
  have eq127135 : (σ y) = (M.op y (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq124326
       have i₂ := eq126103 (σ y)
       grind)
    | exact superpose eq126103 eq124326
    | exact resolve eq124326 eq126103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124326 eq126103
  have eq127379 : (σ y) = (M.op y (σ y)) ∨ x = (M.op x y) := by grind
  clear eq127135
  have eq127403 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq123177 X0 (σ y)
       have i₂ := eq127379
       grind)
    | exact superpose eq127379 eq123177
    | exact resolve eq123177 eq127379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123177 eq127379
  have eq127473 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq127403 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127403
  have eq127695 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq127473 (σ x)
       grind)
    | exact superpose eq127473 eq14
    | exact resolve eq14 eq127473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127473
  have eq127813 : (σ y) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq127695
       have i₂ := eq123645 x
       grind)
    | exact superpose eq123645 eq127695
    | exact resolve eq127695 eq123645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123645 eq127695
  have eq127815 : x = y ∨ x = (M.op x y) := by grind
  clear eq127813
  have eq127816 : x = (M.op x y) := by
    first
    | (have r₁ := eq127815
       have r₂ := eq124230
       grind)
    | exact resolve eq127815 eq124230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124230 eq127815
  have eq127841 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x y
       have i₂ := eq127816
       grind)
    | exact superpose eq127816 eq8
    | exact resolve eq8 eq127816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127846 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op x X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 X1 X2 x y
       have i₂ := eq127816
       grind)
    | exact superpose eq127816 eq18
    | exact resolve eq18 eq127816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq128054 : ∀ X0 : G, (M.op x X0) = (k (M.op x X0) X0) := by
    intro X0
    first
    | (have i₁ := eq24983 X0 x y
       have i₂ := eq127816
       grind)
    | exact superpose eq127816 eq24983
    | exact resolve eq24983 eq127816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24983
  have eq129209 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X0 X0))) = (M.op x X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq108 X2 X0 X1 x x
       have i₂ := eq127841 (M.op x x) X0
       grind)
    | exact superpose eq127841 eq108
    | exact resolve eq108 eq127841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq129516 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq129209 X0 X1 x
       have i₂ := eq127841 x X0
       grind)
    | exact superpose eq127841 eq129209
    | exact resolve eq129209 eq127841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127841 eq129209
  have eq131964 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq129516 y x
       have i₂ := eq127816
       grind)
    | exact superpose eq127816 eq129516
    | exact resolve eq129516 eq127816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133912 : x = (k x x) := by
    first
    | (have i₁ := eq128054 x
       have i₂ := eq131964 x
       grind)
    | exact superpose eq131964 eq128054
    | exact resolve eq128054 eq131964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128054 eq131964
  have eq134758 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq664 x
       have i₂ := eq133912
       grind)
    | exact superpose eq133912 eq664
    | (have j0 := eq664 x
       grind)
    | exact resolve eq664 eq133912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664 eq133912
  have eq134798 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq134758
  have eq136593 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq127846 (σ x) (σ x) X0
       have i₂ := eq134798
       grind)
    | exact superpose eq134798 eq127846
    | exact resolve eq127846 eq134798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127846
  have eq139637 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq136593 (σ y)
       grind)
    | exact superpose eq136593 eq14
    | exact resolve eq14 eq136593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139638 : (σ x) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq134798
       have i₂ := eq136593 (σ x)
       grind)
    | exact superpose eq136593 eq134798
    | exact resolve eq134798 eq136593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134798
  have eq140222 : (σ x) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq139637
       have i₂ := eq127816
       grind)
    | exact superpose eq127816 eq139637
    | exact resolve eq139637 eq127816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127816 eq139637
  have eq140346 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq129516 (σ x) x
       have i₂ := eq139638
       grind)
    | exact superpose eq139638 eq129516
    | exact resolve eq129516 eq139638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129516
  have eq141515 : ∀ X0 : G, (τ (σ x)) = (k X0 (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq116 X0 (σ x)
       have i₂ := eq140346 (σ X0)
       grind)
    | exact superpose eq140346 eq116
    | (have j0 := eq116 X0 (σ x)
       grind)
    | exact resolve eq116 eq140346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq140346
  have eq141635 : ∀ X0 : G, x = (k X0 x) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq141515 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq141515
    | (have j0 := eq141515 X0
       grind)
    | exact resolve eq141515 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141515
  have eq141916 : ∀ X0 : G, (σ x) = (M.op x (σ X0)) ∨ x = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq141635 X0
       have i₂ := eq136593 (σ X0)
       grind)
    | exact superpose eq136593 eq141635
    | (have j0 := eq141635 X0
       grind)
    | exact resolve eq141635 eq136593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136593 eq141635
  have eq171913 : (σ x) ≠ (σ x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq140222
       have i₂ := eq141916 y
       grind)
    | exact superpose eq141916 eq140222
    | (have j1 := eq141916 y
       grind)
    | (have r₁ := eq140222
       have r₂ := eq141916 y
       grind)
    | exact resolve eq140222 eq141916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141916
  have eq172013 : x = (k y x) := by grind
  clear eq171913
  have eq172105 : x = y := by
    first
    | (have i₁ := eq46649
       have i₂ := eq172013
       grind)
    | exact superpose eq172013 eq46649
    | exact resolve eq46649 eq172013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46649 eq172013
  have eq172330 : (σ x) ≠ (M.op x (σ x)) := by
    first
    | (have i₁ := eq140222
       have i₂ := eq172105
       grind)
    | exact superpose eq172105 eq140222
    | exact resolve eq140222 eq172105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140222 eq172105
  have eq172338 : False := by grind
  exact eq172338

/-- `Equation4513`: `x ◇ (y ◇ z) = (x ◇ y) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_y_x_pyx_Equation4513 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4513 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4513.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq17 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X3 X0) X5) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq8 X3 X0 (M.op X1 x) X5
       have i₂ := eq8 X0 X1 x X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq8 X0 X1 x X4
       have i₂ := eq8 X0 X1 x X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 X2 x
       have i₂ := eq8 X0 X1 X3 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X4)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X0 X1 X4 (M.op X2 x)
       have i₂ := eq8 (M.op X0 X1) X2 x X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq33 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq110 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X1 X3) ∨ (k X0 (M.op X1 X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 X0 (M.op X1 X3)
       have i₂ := eq23 X0 X1 X3 X2
       grind)
    | (have i₁ := eq11 X0 (M.op X1 X3)
       have i₂ := eq23 X0 X1 X2 X3
       grind)
    | exact superpose eq23 eq11
    | (have j0 := eq11 X0 (M.op X1 X3)
       grind)
    | (have r₁ := eq11 X0 (M.op X0 (M.op X0 X3))
       have r₂ := eq23 X0 X0 (M.op X0 X3) X3
       grind)
    | (have r₁ := eq11 X0 (M.op X0 (M.op X0 X2))
       have r₂ := eq23 X0 X0 X2 (M.op X0 X2)
       grind)
    | exact resolve eq11 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq40 X1 X0
       have i₂ := eq12 (σ X1) X0
       grind)
    | exact superpose eq12 eq40
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq286 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op (M.op X0 X1) X3) X4) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq17 X4 x x (M.op (M.op X0 X1) X3) X5
       have i₂ := eq24 X0 X1 X3 (M.op (M.op X4 x) x) X2
       grind)
    | exact superpose eq24 eq17
    | exact resolve eq17 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq24
  have eq1738 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq32 X0 X1
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq32 X0 X1
       grind)
    | exact resolve eq11 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1765 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq32 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq1766 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1738 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1738
  have eq1767 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1766 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1766
    | (have j0 := eq1766 X0 X1
       grind)
    | exact resolve eq1766 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1766
  have eq5874 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq33
    | exact resolve eq33 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq5924 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5874 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq5874
    | (have j0 := eq5874 X0 X1
       grind)
    | exact resolve eq5874 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5874
  have eq6200 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq110 X0 X0 x (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq6209 : ∀ X0 X1 X2 X3 X4 : G, (k X0 (M.op X0 (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6200 X0 (M.op X1 x)
       have i₂ := eq286 X0 X1 x X2 X3 X4
       grind)
    | exact superpose eq286 eq6200
    | exact resolve eq6200 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286 eq6200
  have eq18891 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1767 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1767
    | exact resolve eq1767 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18898 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1767 x y
       grind)
    | exact superpose eq1767 eq14
    | (have j1 := eq1767 x y
       grind)
    | exact resolve eq14 eq1767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1767
  have eq18993 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18891 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq18891
    | (have j0 := eq18891 X0 X1
       grind)
    | exact resolve eq18891 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18891
  have eq18995 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18993 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq18993
    | (have j0 := eq18993 X0 X1
       grind)
    | exact resolve eq18993 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq18993
  have eq44134 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18995 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18995
    | exact resolve eq18995 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18995
  have eq44993 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq44134 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44134
  have eq79675 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq18898
       have i₂ := eq5924 y x
       grind)
    | exact superpose eq5924 eq18898
    | (have j1 := eq5924 y x
       grind)
    | (have r₁ := eq18898
       have r₂ := eq5924 y x
       grind)
    | exact resolve eq18898 eq5924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18898
  have eq79676 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq79675
  have eq81158 : (M.op x y) = (τ (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq79676
       grind)
    | exact superpose eq79676 eq9
    | exact resolve eq9 eq79676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79676
  have eq81215 : x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq81158
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq81158
    | exact resolve eq81158 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81158
  have eq82711 : ∀ X0 X1 : G, (M.op y (M.op x X0)) = (M.op x X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq8 y x X0 X1
       have i₂ := eq81215
       grind)
    | exact superpose eq81215 eq8
    | exact resolve eq8 eq81215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82722 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 y X1 x
       have i₂ := eq81215
       grind)
    | exact superpose eq81215 eq23
    | exact resolve eq23 eq81215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82855 : x ≠ x ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44993 x y
       have i₂ := eq81215
       grind)
    | exact superpose eq81215 eq44993
    | (have j0 := eq44993 x y
       grind)
    | (have r₁ := eq44993 x y
       have r₂ := eq81215
       grind)
    | (have r₁ := eq44993 y x
       have r₂ := eq81215
       grind)
    | exact resolve eq44993 eq81215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44993
  have eq82861 : x = (k x y) ∨ y = (M.op x y) := by grind
  clear eq82855
  have eq82863 : x = (k x y) := by
    first
    | (have j1 := eq11 x y
       grind)
    | (have r₁ := eq82861
       have r₂ := eq11 x y
       grind)
    | exact resolve eq82861 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82861
  have eq83290 : (σ x) = (σ (M.op y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5924 x y
       have i₂ := eq82863
       grind)
    | exact superpose eq82863 eq5924
    | (have j0 := eq5924 x y
       grind)
    | exact resolve eq5924 eq82863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5924
  have eq111168 : ∀ X0 X1 : G, (M.op X1 x) = (M.op X1 (M.op x X0)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq82722 X1 (M.op x x)
       have i₂ := eq82711 x X0
       grind)
    | exact superpose eq82711 eq82722
    | exact resolve eq82722 eq82711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82722
  have eq111998 : ∀ X0 X1 : G, (M.op X1 x) = (M.op X1 (M.op x X0)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq111168 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111168
  have eq132535 : ∀ X1 : G, (M.op y x) = (M.op x X1) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq82711 x X1
       have i₂ := eq111998 x y
       grind)
    | exact superpose eq111998 eq82711
    | exact resolve eq82711 eq111998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82711 eq111998
  have eq132541 : ∀ X1 : G, (M.op y x) = (M.op x X1) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have j0 := eq132535 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132535
  have eq135804 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq81215
       have i₂ := eq132541 X0
       grind)
    | exact superpose eq132541 eq81215
    | exact resolve eq81215 eq132541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81215
  have eq135807 : ∀ X0 : G, (σ x) = (σ (M.op x X0)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq83290
       have i₂ := eq132541 X0
       grind)
    | exact superpose eq132541 eq83290
    | exact resolve eq83290 eq132541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83290 eq132541
  have eq136390 : ∀ X0 : G, (σ x) = (σ (M.op x X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq135807 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135807
  have eq136393 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq135804 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135804
  have eq136948 : x = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6209 x x x x x
       have i₂ := eq136393 (M.op (M.op (M.op (M.op x x) x) x) x)
       grind)
    | exact superpose eq136393 eq6209
    | exact resolve eq6209 eq136393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136393
  have eq137559 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1765 x
       have i₂ := eq136948
       grind)
    | exact superpose eq136948 eq1765
    | (have j0 := eq1765 x
       grind)
    | exact resolve eq1765 eq136948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136948
  have eq137568 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq137559
  have eq163648 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ x) (σ x) x x
       have i₂ := eq137568
       grind)
    | exact superpose eq137568 eq19
    | exact resolve eq19 eq137568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235785 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq137568
       have i₂ := eq163648 (σ x) X0
       grind)
    | (have i₁ := eq137568
       have i₂ := eq163648 X0 (σ x)
       grind)
    | exact superpose eq163648 eq137568
    | exact resolve eq137568 eq163648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137568 eq163648
  have eq235917 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq235785 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235785
  have eq236031 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq235917 (σ y)
       grind)
    | exact superpose eq235917 eq14
    | exact resolve eq14 eq235917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235917
  have eq236315 : y = (M.op x y) := by
    first
    | (have r₁ := eq236031
       have r₂ := eq136390 y
       grind)
    | exact resolve eq236031 eq136390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136390 eq236031
  have eq236361 : ∀ X0 X1 : G, (M.op y X1) = (M.op x (M.op y X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 x y X0 X1
       have i₂ := eq236315
       grind)
    | exact superpose eq236315 eq8
    | exact resolve eq8 eq236315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236372 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 x X1 y
       have i₂ := eq236315
       grind)
    | exact superpose eq236315 eq23
    | exact resolve eq23 eq236315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq238877 : ∀ X0 X1 : G, (M.op y X1) = (M.op x (M.op x (M.op y X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq236361 x X1
       have i₂ := eq236361 X0 x
       grind)
    | exact superpose eq236361 eq236361
    | exact resolve eq236361 eq236361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236361
  have eq240098 : ∀ X1 : G, (M.op x y) = (M.op y X1) := by
    intro X1
    first
    | (have i₁ := eq238877 x X1
       have i₂ := eq236372 x (M.op y x)
       grind)
    | exact superpose eq236372 eq238877
    | exact resolve eq238877 eq236372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236372 eq238877
  have eq240106 : ∀ X1 : G, y = (M.op y X1) := by
    intro X1
    first
    | (have i₁ := eq240098 X1
       have i₂ := eq236315
       grind)
    | exact superpose eq236315 eq240098
    | exact resolve eq240098 eq236315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240098
  have eq241007 : y = (k y y) := by
    first
    | (have i₁ := eq6209 y x x x x
       have i₂ := eq240106 (M.op (M.op (M.op (M.op y x) x) x) x)
       grind)
    | exact superpose eq240106 eq6209
    | exact resolve eq6209 eq240106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6209
  have eq241423 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1765 y
       have i₂ := eq241007
       grind)
    | exact superpose eq241007 eq1765
    | (have j0 := eq1765 y
       grind)
    | exact resolve eq1765 eq241007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1765 eq241007
  have eq241433 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq241423
  have eq241543 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (σ y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ y) (σ y) x x
       have i₂ := eq241433
       grind)
    | exact superpose eq241433 eq19
    | exact resolve eq19 eq241433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq250096 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq241433
       have i₂ := eq241543 (σ y) X0
       grind)
    | (have i₁ := eq241433
       have i₂ := eq241543 X0 (σ y)
       grind)
    | exact superpose eq241543 eq241433
    | exact resolve eq241433 eq241543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241433 eq241543
  have eq251054 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq118 (σ y) X0
       have i₂ := eq250096 (σ X0)
       grind)
    | exact superpose eq250096 eq118
    | (have j0 := eq118 (σ y) X0
       grind)
    | exact resolve eq118 eq250096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq251079 : ∀ X0 : G, (σ y) = (M.op (σ X0) (σ y)) ∨ y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq251054 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq251054
    | (have j0 := eq251054 X0
       grind)
    | exact resolve eq251054 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251054
  have eq354203 : (σ (M.op x y)) ≠ (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq251079 x
       grind)
    | exact superpose eq251079 eq14
    | (have j1 := eq251079 x
       grind)
    | exact resolve eq14 eq251079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251079
  have eq354287 : (σ y) ≠ (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq354203
       have i₂ := eq236315
       grind)
    | exact superpose eq236315 eq354203
    | exact resolve eq354203 eq236315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236315 eq354203
  have eq354288 : y = (k x y) := by grind
  clear eq354287
  have eq354294 : x = y := by
    first
    | (have i₁ := eq354288
       have i₂ := eq82863
       grind)
    | exact superpose eq82863 eq354288
    | exact resolve eq354288 eq82863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82863 eq354288
  have eq354313 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq354294
       grind)
    | exact superpose eq354294 eq14
    | exact resolve eq14 eq354294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354534 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq240106 x
       have i₂ := eq354294
       grind)
    | exact superpose eq354294 eq240106
    | exact resolve eq240106 eq354294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240106
  have eq354580 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq250096 X0
       have i₂ := eq354294
       grind)
    | exact superpose eq354294 eq250096
    | exact resolve eq250096 eq354294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250096 eq354294
  have eq354695 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq354313
       have i₂ := eq354534 x
       grind)
    | exact superpose eq354534 eq354313
    | exact resolve eq354313 eq354534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354313 eq354534
  have eq354750 : False := by grind
  exact eq354750

/-- `Equation4517`: `x ◇ (y ◇ z) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pxy_Equation4517 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4517 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4517.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X2) X3) := by
    intro X0 X1 X2 X3
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
  have eq17 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X4 X1)) X5) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq8 X3 X0 (M.op X4 X1) X5
       have i₂ := eq8 X0 X4 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X4) X5) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq8 X3 (M.op X0 X2) X4 X5
       have i₂ := eq8 X0 X1 X2 X4
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq8 X0 x X1 X4
       have i₂ := eq8 X0 x X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 X2 x
       have i₂ := eq8 X0 X3 X2 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 X1)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X0 X4 X1 (M.op x X2)
       have i₂ := eq8 (M.op X0 X1) x X2 X3
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
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9
    | exact resolve eq9 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
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
  have eq36 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X2) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X0 X0 X2
       have i₂ := eq12 X3 X0
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq40 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
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
  have eq41 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq34 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq78 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq106 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X0 X1) X2)) = (M.op X3 (M.op X4 X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq23 X3 X4 X5 (M.op X0 X1)
       have i₂ := eq19 X0 X1 X5 X2
       grind)
    | (have i₁ := eq23 X3 X4 X5 (M.op X0 X1)
       have i₂ := eq19 X0 X1 X2 X5
       grind)
    | exact superpose eq19 eq23
    | exact resolve eq23 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq153 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (M.op X2 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq41 X1 (τ X0) X2
       grind)
    | exact superpose eq41 eq15
    | (have j1 := eq41 X1 X1 X2
       grind)
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq157 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq41 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq41 eq13
    | (have j1 := eq41 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq41 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq163 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = X0 ∨ (M.op X2 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq153 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq153
    | (have j0 := eq153 X0 X1 X2
       grind)
    | exact resolve eq153 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq209 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq18 x x x X0 X1 X2
       have i₂ := eq18 x x x X0 X3 X4
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq311 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X0 (M.op X6 X1)) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X5) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq24 X0 X1 X2 (M.op x X3) X6
       have i₂ := eq24 (M.op (M.op X0 X1) X2) X3 X4 X5 x
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op (M.op X0 X2) X3) X4) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq18 x x x (M.op (M.op X0 X2) X3) X4 X5
       have i₂ := eq24 X0 X2 X3 (M.op x (M.op x x)) X1
       grind)
    | exact superpose eq24 eq18
    | exact resolve eq18 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq483 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X4 X2)) ≠ (M.op X0 (M.op (M.op X1 X2) X3)) ∨ (M.op X0 (M.op X4 X2)) = (k (M.op X0 (M.op X4 X2)) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq162 (M.op X0 (M.op X4 X2)) X5
       have i₂ := eq17 X1 X2 X3 X0 X4 X5
       grind)
    | exact superpose eq17 eq162
    | (have j0 := eq162 (M.op X0 (M.op X4 X2)) X5
       grind)
    | (have r₁ := eq162 (M.op X3 (M.op (M.op X0 X2) X2)) X5
       have r₂ := eq17 X0 X2 X2 X3 (M.op X0 X2) X5
       grind)
    | exact resolve eq162 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq162
  have eq517 : ∀ X0 X2 X4 X5 : G, (M.op X0 (M.op X4 X2)) = (k (M.op X0 (M.op X4 X2)) X5) := by
    intro X0 X2 X4 X5
    first
    | (have j0 := eq483 X0 x X2 x X4 X5
       grind)
    | (have r₁ := eq483 x x X2 X5 (M.op X0 x) X5
       have r₂ := eq106 X0 x X2 x (M.op x X2) X5
       grind)
    | (have r₁ := eq483 x X0 x X2 X4 X5
       have r₂ := eq106 X0 x X2 x X4 x
       grind)
    | exact resolve eq483 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq483
  have eq1306 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = X0 ∨ (k X2 X0) = (M.op X2 X0) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq36 X1 X1 X2 X3
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq36
    | (have j0 := eq36 X0 X1 X2 X2
       have j1 := eq12 X2 X0
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1567 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X0 X3 X4 x
       have i₂ := eq209 X0 X4 x X1 X2
       grind)
    | (have i₁ := eq8 X0 X3 X4 x
       have i₂ := eq209 X0 X1 X2 X4 x
       grind)
    | exact superpose eq209 eq8
    | exact resolve eq8 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq1788 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X0 X1 X2 x
       have i₂ := eq1567 X0 X2 x X3 X4
       grind)
    | exact superpose eq1567 eq8
    | exact resolve eq8 eq1567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1567
  have eq1935 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ X0)
       have i₂ := eq39 X0 X0
       grind)
    | exact superpose eq39 eq11
    | (have j0 := eq11 X1 (σ X0)
       have j1 := eq39 X0 X0
       grind)
    | (have r₁ := eq11 X0 (σ X1)
       have r₂ := eq39 X0 X1
       grind)
    | exact resolve eq11 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1975 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) X1) = (M.op (σ X0) X2) ∨ (σ (k X3 X0)) = (M.op (σ X3) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 (σ X1) (σ X1) X2 x
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq19
    | (have j1 := eq39 X3 X0
       grind)
    | exact resolve eq19 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2000 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq39 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq2005 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1935 X0 X1
       have j1 := eq11 X1 (σ X0)
       grind)
    | (have r₁ := eq1935 X0 X1
       have r₂ := eq11 X0 (σ X0)
       grind)
    | exact resolve eq1935 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1935
  have eq6652 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2005 (τ X0) X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq2005
    | (have j0 := eq2005 (τ X0) X1
       grind)
    | exact resolve eq2005 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2005
  have eq6669 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6652 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6652
    | (have j0 := eq6652 X0 X1
       grind)
    | exact resolve eq6652 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6652
  have eq6678 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6669 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6669
    | (have j0 := eq6669 X0 X1
       grind)
    | exact resolve eq6669 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6669
  have eq7125 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6678 (τ X0) X1
       have i₂ := eq78 X0 X0
       grind)
    | exact superpose eq78 eq6678
    | (have j0 := eq6678 (τ X0) X1
       grind)
    | exact resolve eq6678 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6678
  have eq7493 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq40 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq40
    | (have j0 := eq40 X0 X1
       grind)
    | exact resolve eq40 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq7721 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7493 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq7493
    | (have j0 := eq7493 X0 X1
       grind)
    | exact resolve eq7493 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7493
  have eq15678 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2000 X0
       have i₂ := eq163 X1 X0 X0
       grind)
    | exact superpose eq163 eq2000
    | (have j0 := eq2000 X0
       have j1 := eq163 X1 X0 x
       grind)
    | exact resolve eq2000 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq15712 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2000 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq2000
    | (have j0 := eq2000 (τ X0)
       grind)
    | exact resolve eq2000 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2000
  have eq15741 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq15712 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15712
    | (have j0 := eq15712 X0
       grind)
    | exact resolve eq15712 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15712
  have eq15754 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq15678 X0 X1
       have j1 := eq11 X1 (σ X0)
       grind)
    | (have r₁ := eq15678 X0 X1
       have r₂ := eq11 X0 (σ X0)
       grind)
    | exact resolve eq15678 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15678
  have eq15755 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15741 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15741
    | (have j0 := eq15741 X0
       grind)
    | exact resolve eq15741 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15741
  have eq17033 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k X1 (σ X0)) = X1 ∨ (σ (M.op X2 X0)) = (σ (k X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15754 X0 X1
       have i₂ := eq7721 X2 X0
       grind)
    | exact superpose eq7721 eq15754
    | (have j0 := eq15754 X0 X1
       have j1 := eq7721 X2 X0
       grind)
    | exact resolve eq15754 eq7721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7721 eq15754
  have eq17246 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = X1 ∨ (σ (M.op X2 X0)) = (σ (k X2 X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq17033 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17033
  have eq17309 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq157 x y X0
       grind)
    | exact superpose eq157 eq14
    | (have j1 := eq157 X0 y X0
       grind)
    | exact resolve eq14 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq17447 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq17309 X0
       have j1 := eq17246 y X0 x
       grind)
    | (have r₁ := eq17309 X0
       have r₂ := eq17246 y x x
       grind)
    | exact resolve eq17309 eq17246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17246 eq17309
  have eq17478 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq15755 (σ y)
       have i₂ := eq17447 (σ y)
       grind)
    | exact superpose eq17447 eq15755
    | (have j0 := eq15755 (σ y)
       grind)
    | (have r₁ := eq15755 (σ y)
       have r₂ := eq17447 (σ y)
       grind)
    | exact resolve eq15755 eq17447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17480 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k X0 (τ (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq7125 (σ y) X0
       have i₂ := eq17447 (σ y)
       grind)
    | exact superpose eq17447 eq7125
    | (have j0 := eq7125 (σ y) X0
       grind)
    | exact resolve eq7125 eq17447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7125 eq17447
  have eq17504 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq17480 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17480
  have eq17506 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq17478
  have eq17512 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq17504 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq17504
    | exact resolve eq17504 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17504
  have eq17706 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq15755 y
       have i₂ := eq17512 y
       grind)
    | exact superpose eq17512 eq15755
    | (have j0 := eq15755 y
       grind)
    | (have r₁ := eq15755 y
       have r₂ := eq17512 y
       grind)
    | exact resolve eq15755 eq17512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15755 eq17512
  have eq17731 : y = (M.op y y) := by grind
  clear eq17706
  have eq18506 : ∀ X0 X1 : G, (M.op y X1) = (M.op y X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 y y x x
       have i₂ := eq17731
       grind)
    | exact superpose eq17731 eq19
    | exact resolve eq19 eq17731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq18569 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1788 X0 X1 X2 y y
       have i₂ := eq17731
       grind)
    | exact superpose eq17731 eq1788
    | exact resolve eq1788 eq17731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20097 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X5) X6) X7) X8) X9) = (M.op X0 (M.op X10 X1)) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10
    first
    | (have i₁ := eq311 X0 X1 X2 X3 X4 (M.op x X5) X10
       have i₂ := eq311 (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X5 X6 X7 X8 X9 x
       grind)
    | exact superpose eq311 eq311
    | exact resolve eq311 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20544 : ∀ X0 X1 X2 X3 X4 X5 X7 X8 X9 X10 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X2) X3) X4) X5) X7) X8) X9) X10) := by
    intro X0 X1 X2 X3 X4 X5 X7 X8 X9 X10
    first
    | (have i₁ := eq354 (M.op (M.op (M.op (M.op X0 X2) X3) X4) X5) x X7 X8 X9 X10
       have i₂ := eq311 X0 X2 X3 X4 X5 (M.op x X7) X1
       grind)
    | exact superpose eq311 eq354
    | exact resolve eq354 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311 eq354
  have eq20579 : ∀ X0 X2 X3 X4 X5 X7 X8 X9 X10 : G, (M.op X0 y) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X2) X3) X4) X5) X7) X8) X9) X10) := by
    intro X0 X2 X3 X4 X5 X7 X8 X9 X10
    first
    | (have i₁ := eq20544 X0 x X2 X3 X4 X5 X7 X8 X9 X10
       have i₂ := eq18569 X0 x X2
       grind)
    | exact superpose eq18569 eq20544
    | exact resolve eq20544 eq18569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20544
  have eq20614 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G, (M.op X0 y) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X5) X6) X7) X8) X9) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7 X8 X9
    first
    | (have i₁ := eq20097 X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 x
       have i₂ := eq18569 X0 x X1
       grind)
    | exact superpose eq18569 eq20097
    | exact resolve eq20097 eq18569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20097
  have eq20648 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op X0 X1) y) := by
    intro X0 X1
    first
    | (have i₁ := eq20614 X0 X1 x x x x x x x x
       have i₂ := eq20579 (M.op X0 X1) x x x x x x x x
       grind)
    | exact superpose eq20579 eq20614
    | exact resolve eq20614 eq20579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20579 eq20614
  have eq24222 : ∀ X0 : G, y = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq17731
       have i₂ := eq18506 X0 y
       grind)
    | (have i₁ := eq17731
       have i₂ := eq18506 y X0
       grind)
    | exact superpose eq18506 eq17731
    | exact resolve eq17731 eq18506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17731 eq18506
  have eq25646 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 y x x X0 X1 X2
       have i₂ := eq24222 (M.op x x)
       grind)
    | exact superpose eq24222 eq18
    | exact resolve eq18 eq24222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq24222
  have eq30555 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1788 X0 X1 X2 (σ y) (σ y)
       have i₂ := eq17506
       grind)
    | exact superpose eq17506 eq1788
    | exact resolve eq1788 eq17506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1788 eq17506
  have eq30568 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq30555 X0 x x
       have i₂ := eq18569 X0 x x
       grind)
    | exact superpose eq18569 eq30555
    | exact resolve eq30555 eq18569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30555
  have eq34173 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq30568 (σ x)
       grind)
    | exact superpose eq30568 eq14
    | exact resolve eq14 eq30568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30568
  have eq52143 : ∀ X0 X3 X4 X5 : G, (k X0 X3) = X0 ∨ (M.op X4 X0) = (k X4 X0) ∨ (k X5 X0) = (M.op X5 X0) := by
    intro X0 X3 X4 X5
    first
    | (have i₁ := eq517 X0 x X4 X5
       have i₂ := eq1306 X0 (M.op X4 x) x X3
       grind)
    | exact superpose eq1306 eq517
    | (have j1 := eq1306 X0 x X4 X4
       grind)
    | exact resolve eq517 eq1306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq52486 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X2) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1306 X1 X2 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306
  have eq52487 : ∀ X0 X1 X2 : G, (M.op X1 X2) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq52486 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52486
  have eq55450 : ∀ X0 X1 : G, (M.op (σ X0) X1) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1975 X0 X1 x X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1975
  have eq348611 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq55450 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq55450
    | exact resolve eq55450 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55450
  have eq348964 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq348611 X0 X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq348611
    | (have j0 := eq348611 X0 X1
       grind)
    | exact resolve eq348611 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348611
  have eq348968 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq348964 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq348964
    | (have j0 := eq348964 X0 X1
       grind)
    | exact resolve eq348964 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348964
  have eq348971 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X1) ≠ (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq348968 X0 X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq348968
    | (have j0 := eq348968 X0 X1
       grind)
    | exact resolve eq348968 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq348968
  have eq348972 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq348971 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq348971
    | (have j0 := eq348971 X0 X1
       grind)
    | exact resolve eq348971 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348971
  have eq355563 : ∀ X0 X2 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq348972 X0 x
       have i₂ := eq52487 X2 X0 x
       grind)
    | exact superpose eq52487 eq348972
    | (have j0 := eq348972 X0 x
       have j1 := eq52487 X0 X0 X2
       grind)
    | (have r₁ := eq348972 x x
       have r₂ := eq52487 x x X2
       grind)
    | exact resolve eq348972 eq52487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52487 eq348972
  have eq355673 : ∀ X0 X2 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X2
    first
    | (have j0 := eq355563 X0 X0
       have j1 := eq52143 X0 x X0 X0
       grind)
    | (have r₁ := eq355563 x X2
       have r₂ := eq52143 x x x x
       grind)
    | exact resolve eq355563 eq52143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52143 eq355563
  have eq385693 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq355673 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355673
  have eq385694 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq385693 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385693
  have eq386121 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq78 X0 X0
       have i₂ := eq385694 (τ X0)
       grind)
    | exact superpose eq385694 eq78
    | exact resolve eq78 eq385694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq386138 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq386121 X0
       have i₂ := eq385694 X0
       grind)
    | exact superpose eq385694 eq386121
    | exact resolve eq386121 eq385694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385694 eq386121
  have eq387136 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18569 X1 (τ X0) (τ X0)
       have i₂ := eq386138 X0
       grind)
    | exact superpose eq386138 eq18569
    | exact resolve eq18569 eq386138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387141 : ∀ X0 X1 : G, (M.op (τ X0) y) = (M.op (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25646 (τ X0) (τ X0) X1
       have i₂ := eq386138 X0
       grind)
    | exact superpose eq386138 eq25646
    | exact resolve eq25646 eq386138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25646
  have eq390352 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) y) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq386138 (M.op X0 X0)
       have i₂ := eq387136 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq387136 eq386138
    | exact resolve eq386138 eq387136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386138 eq387136
  have eq390417 : ∀ X0 : G, (τ (M.op (M.op X0 X0) y)) = (M.op (τ (M.op X0 X0)) y) := by
    intro X0
    first
    | (have i₁ := eq390352 X0
       have i₂ := eq18569 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq18569 eq390352
    | exact resolve eq390352 eq18569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18569 eq390352
  have eq390582 : ∀ X0 : G, (M.op (τ X0) y) = (τ (M.op (M.op X0 X0) y)) := by
    intro X0
    first
    | (have i₁ := eq390417 X0
       have i₂ := eq387141 X0 y
       grind)
    | exact superpose eq387141 eq390417
    | exact resolve eq390417 eq387141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387141 eq390417
  have eq390601 : ∀ X0 : G, (M.op (τ X0) y) = (τ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq390582 X0
       have i₂ := eq20648 X0 X0
       grind)
    | exact superpose eq20648 eq390582
    | exact resolve eq390582 eq20648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20648 eq390582
  have eq390819 : ∀ X0 : G, (M.op X0 y) = (σ (M.op (τ X0) y)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 y)
       have i₂ := eq390601 X0
       grind)
    | exact superpose eq390601 eq10
    | exact resolve eq10 eq390601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390601
  have eq391153 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) y) := by
    intro X0
    first
    | (have i₁ := eq390819 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq390819
    | exact resolve eq390819 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390819
  have eq391576 : (M.op (σ x) y) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq34173
       have i₂ := eq391153 x
       grind)
    | exact superpose eq391153 eq34173
    | (have r₁ := eq34173
       have r₂ := eq391153 x
       grind)
    | exact resolve eq34173 eq391153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34173 eq391153
  have eq391605 : False := by grind
  exact eq391605

/-- `Equation4541`: `x ◇ (y ◇ z) = (z ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation4541 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4541 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4541.models_iff G M).mp hM
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
  have eq61 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq117 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq121 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq117 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq117 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq117 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq117 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq139 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq121 (σ X0) (σ X1)
       grind)
    | exact superpose eq121 eq13
    | exact resolve eq13 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq139 X0 X1
       have i₂ := eq121 X0 X1
       grind)
    | exact superpose eq121 eq139
    | exact resolve eq139 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq139
  have eq2573 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq146 x y
       grind)
    | exact superpose eq146 eq14
    | (have r₁ := eq14
       have r₂ := eq146 x y
       grind)
    | exact resolve eq14 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq2596 : False := by grind
  exact eq2596
