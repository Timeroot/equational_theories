import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation695`: `x = y ◇ (x ◇ ((z ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_pxx_pxy_Equation695 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law695 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law695.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X2 X2) X1))) = X0 := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2))) (M.op X3 X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2))) X2
       have i₂ := eq8 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op (M.op X1 X1) X2) X0
       have i₂ := eq8 (M.op X0 X0) X2 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq40 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (k X0 X2) = (M.op X0 X2) := by
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
  have eq44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq48 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq40 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = X1 ∨ (k X0 X3) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 X2 X0 X1
       have i₂ := eq12 X0 X3
       grind)
    | exact superpose eq12 eq22
    | (have j1 := eq12 X0 X3
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X2 (M.op X0 X0) (M.op X1 X1)
       have i₂ := eq22 X1 X0 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (M.op X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X1 X1) (M.op X0 X0)
       have i₂ := eq22 X1 X0 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X1 X1) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (M.op X2 X2) (M.op (M.op X1 X1) X0)) (M.op (M.op X1 X1) X0) X2
       have i₂ := eq22 (M.op (M.op X2 X2) (M.op (M.op X1 X1) X0)) X1 X0
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) ≠ (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1))) ∨ (M.op (M.op X0 X0) (M.op X1 X1)) = (k (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) (M.op (M.op X1 X1) (M.op X2 X2))) X1
       have i₂ := eq21 (M.op (M.op X1 X1) (M.op X2 X2)) X1 X2 (M.op (M.op X1 X1) (M.op X2 X2))
       grind)
    | exact superpose eq21 eq11
    | (have j0 := eq11 (M.op (M.op X0 X0) (M.op X1 X1)) X1
       grind)
    | exact resolve eq11 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X2) X3) (M.op (M.op X0 X0) (M.op X1 X1))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1))) X2 X3
       have i₂ := eq21 (M.op (M.op X0 X0) (M.op X1 X1)) X0 X1 (M.op (M.op X0 X0) (M.op X1 X1))
       grind)
    | exact superpose eq21 eq22
    | exact resolve eq22 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (k (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq141 X0 X1 X2
       grind)
    | (have r₁ := eq141 X0 X0 X2
       have r₂ := eq64 (M.op X0 X0) (M.op X0 X0) (M.op X0 X0)
       grind)
    | (have r₁ := eq141 X0 X2 X2
       have r₂ := eq64 X0 (M.op (M.op X0 X0) (M.op X2 X2)) X2
       grind)
    | exact resolve eq141 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq151 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (k (M.op X1 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq146 X0 X1 X2
       have i₂ := eq143 X0 X1 X0 (M.op X1 X1)
       grind)
    | exact superpose eq143 eq146
    | exact resolve eq146 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq146
  have eq189 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 x X1 (M.op X1 X1)
       have i₂ := eq64 (M.op X1 X1) X0 x
       grind)
    | (have i₁ := eq22 (M.op X1 X1) X1 (M.op X1 X1)
       have i₂ := eq64 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq64 eq22
    | exact resolve eq22 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq323 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq44 x y
       grind)
    | exact superpose eq44 eq14
    | (have j1 := eq44 x x
       grind)
    | exact resolve eq14 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq337 : ∀ X0 X1 X2 X3 : G, (σ X0) = (M.op (M.op (σ X1) (M.op (M.op X2 X2) (M.op X3 X3))) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 (σ X1) X2 X3 (σ X0)
       have i₂ := eq44 X0 X1
       grind)
    | exact superpose eq44 eq21
    | (have j1 := eq44 X0 X1
       grind)
    | exact resolve eq21 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq353 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq44 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq456 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 X3)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq22 X3 x (M.op X0 (M.op X2 X2))
       have i₂ := eq71 X2 x X0
       grind)
    | exact superpose eq71 eq22
    | exact resolve eq22 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq71
  have eq990 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op (k (M.op X0 X0) X1) X2))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X2 (M.op X0 X0)
       have i₂ := eq151 X0 X0 X1
       grind)
    | exact superpose eq151 eq8
    | exact resolve eq8 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1008 : ∀ X0 X1 X2 X3 : G, (M.op (k (M.op X0 X0) X1) (M.op (M.op X2 X2) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq73 X3 X2 (M.op X0 X0)
       have i₂ := eq151 X0 X0 X1
       grind)
    | exact superpose eq151 eq73
    | exact resolve eq73 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq1012 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq189 X2 (M.op X0 X0)
       have i₂ := eq151 X0 X0 X1
       grind)
    | exact superpose eq151 eq189
    | exact resolve eq189 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq1132 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (k (σ (M.op X1 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1)
       have i₂ := eq1012 X1 (τ X2) X0
       grind)
    | exact superpose eq1012 eq16
    | exact resolve eq16 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1133 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) = (k (τ (M.op X1 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 (M.op X1 X1) X2
       have i₂ := eq1012 X1 (σ X2) X0
       grind)
    | exact superpose eq1012 eq20
    | exact resolve eq20 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012
  have eq3740 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1132 X0 x x
       have i₂ := eq1132 X1 x x
       grind)
    | exact superpose eq1132 eq1132
    | exact resolve eq1132 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132
  have eq4675 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1133 X0 x x
       have i₂ := eq1133 X1 x x
       grind)
    | exact superpose eq1133 eq1133
    | exact resolve eq1133 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133
  have eq4746 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq353 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq353
    | (have j0 := eq353 (τ X0)
       grind)
    | exact resolve eq353 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4752 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4746 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4746
    | (have j0 := eq4746 X0
       grind)
    | exact resolve eq4746 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4746
  have eq4766 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4752 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4752
    | (have j0 := eq4752 X0
       grind)
    | exact resolve eq4752 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4752
  have eq7982 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq323
       have i₂ := eq48 x X0 y
       grind)
    | exact superpose eq48 eq323
    | (have j1 := eq48 x X0 x
       grind)
    | exact resolve eq323 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq323
  have eq7985 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x X0) := by
    intro X0
    first
    | (have j0 := eq7982 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7982
  have eq18067 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) X0) ∨ x = (k x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ x) X1
       have i₂ := eq7985 X0
       grind)
    | exact superpose eq7985 eq11
    | (have j1 := eq7985 X1
       grind)
    | (have r₁ := eq11 (σ x) X1
       have r₂ := eq7985 X0
       grind)
    | exact resolve eq11 eq7985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7985
  have eq18199 : ∀ X0 X1 : G, (σ x) = (k (σ x) X0) ∨ x = (k x X1) := by
    intro X0 X1
    first
    | (have j0 := eq18067 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18067
  have eq26651 : ∀ X0 X1 : G, (τ (σ x)) = (k (τ (σ x)) X0) ∨ x = (k x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ x) X0
       have i₂ := eq18199 (σ X0) X1
       grind)
    | exact superpose eq18199 eq20
    | (have j1 := eq18199 X0 X1
       grind)
    | exact resolve eq20 eq18199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18199
  have eq26678 : ∀ X0 X1 : G, x = (k x X0) ∨ x = (k x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26651 X0 X1
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq26651
    | (have j0 := eq26651 X0 X0
       grind)
    | exact resolve eq26651 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26651
  have eq27153 : ∀ X0 : G, x ≠ x ∨ x = (k x X0) := by
    intro X0
    first
    | (have j0 := eq26678 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26678
  have eq27154 : ∀ X0 : G, x = (k x X0) := by
    intro X0
    first
    | (have j0 := eq27153 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27153
  have eq27581 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4766 x
       have i₂ := eq27154 x
       grind)
    | exact superpose eq27154 eq4766
    | (have j0 := eq4766 x
       grind)
    | (have r₁ := eq4766 x
       have r₂ := eq27154 x
       grind)
    | exact resolve eq4766 eq27154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27582 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq353 x
       have i₂ := eq27154 x
       grind)
    | exact superpose eq27154 eq353
    | (have j0 := eq353 x
       grind)
    | exact resolve eq353 eq27154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq27604 : ∀ X0 : G, (τ x) = (k (τ x) X0) := by
    intro X0
    first
    | (have i₁ := eq20 x X0
       have i₂ := eq27154 (σ X0)
       grind)
    | exact superpose eq27154 eq20
    | exact resolve eq20 eq27154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq27609 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq27582
  have eq27610 : x = (M.op x x) := by grind
  clear eq27581
  have eq27828 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq189 X0 x
       have i₂ := eq27610
       grind)
    | exact superpose eq27610 eq189
    | exact resolve eq189 eq27610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq27848 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq456 X0 X1 x
       have i₂ := eq27610
       grind)
    | exact superpose eq27610 eq456
    | exact resolve eq456 eq27610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq27887 : ∀ X0 : G, (σ x) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3740 X0 x
       have i₂ := eq27610
       grind)
    | exact superpose eq27610 eq3740
    | exact resolve eq3740 eq27610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3740
  have eq27890 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ x) := by
    intro X0
    first
    | (have i₁ := eq4675 X0 x
       have i₂ := eq27610
       grind)
    | exact superpose eq27610 eq4675
    | exact resolve eq4675 eq27610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4675 eq27610
  have eq29380 : ∀ X0 X1 X2 : G, (M.op (k (M.op X1 X1) X2) X0) = (M.op X0 x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq990 X1 X2 X0 (M.op (k (M.op X1 X1) X2) X0)
       have i₂ := eq27828 (M.op (k (M.op X1 X1) X2) X0)
       grind)
    | exact superpose eq27828 eq990
    | exact resolve eq990 eq27828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq29524 : ∀ X0 X2 : G, (M.op X0 x) = (M.op (k x X2) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq29380 X0 x X2
       have i₂ := eq27828 x
       grind)
    | exact superpose eq27828 eq29380
    | exact resolve eq29380 eq27828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29380
  have eq29689 : ∀ X0 : G, (M.op x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq29524 X0 x
       have i₂ := eq27154 x
       grind)
    | exact superpose eq27154 eq29524
    | exact resolve eq29524 eq27154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29524
  have eq31961 : (τ x) ≠ (τ x) ∨ (τ x) = (M.op (τ x) (τ x)) := by
    first
    | (have i₁ := eq4766 (τ x)
       have i₂ := eq27604 (τ x)
       grind)
    | exact superpose eq27604 eq4766
    | (have j0 := eq4766 (τ x)
       grind)
    | (have r₁ := eq4766 (τ x)
       have r₂ := eq27604 (τ x)
       grind)
    | exact resolve eq4766 eq27604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4766 eq27604
  have eq31991 : (τ x) = (M.op (τ x) (τ x)) := by grind
  clear eq31961
  have eq32013 : x = (τ x) := by
    first
    | (have i₁ := eq31991
       have i₂ := eq27828 (τ x)
       grind)
    | exact superpose eq27828 eq31991
    | exact resolve eq31991 eq27828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31991
  have eq34161 : x = (σ x) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq32013
       grind)
    | exact superpose eq32013 eq10
    | exact resolve eq10 eq32013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34163 : ∀ X0 : G, (k (σ X0) x) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq16 x X0
       have i₂ := eq32013
       grind)
    | exact superpose eq32013 eq16
    | exact resolve eq16 eq32013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq36156 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq34161
       grind)
    | exact superpose eq34161 eq14
    | exact resolve eq14 eq34161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34161
  have eq43371 : ∀ X0 X1 : G, (τ X0) = (τ x) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq27890 (M.op X0 X0)
       have i₂ := eq62 X0 X0 X0 X1
       grind)
    | exact superpose eq62 eq27890
    | (have j1 := eq62 X0 X1 x X1
       grind)
    | exact resolve eq27890 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq27890
  have eq43494 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (τ X0) = x := by
    intro X0 X1
    first
    | (have i₁ := eq43371 X0 X1
       have i₂ := eq32013
       grind)
    | exact superpose eq32013 eq43371
    | (have j0 := eq43371 X0 X1
       grind)
    | exact resolve eq43371 eq32013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32013 eq43371
  have eq47452 : ∀ X0 X1 X2 X3 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X1)) (M.op (M.op X2 X2) (M.op X3 X3))) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq337 (τ X0) (τ X1) X2 X3
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq337
    | (have j0 := eq337 (τ X0) X1 X2 X3
       grind)
    | exact resolve eq337 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq337
  have eq47960 : ∀ X0 X1 X2 X3 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X1)) (M.op (M.op X2 X2) (M.op X3 X3))) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq47452 X0 X1 X2 X3
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq47452
    | (have j0 := eq47452 X0 X1 X2 X3
       grind)
    | exact resolve eq47452 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47452
  have eq48399 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X1)) (M.op (M.op X2 X2) x)) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47960 X0 X1 X2 x
       have i₂ := eq27848 (M.op X2 X2) x
       grind)
    | exact superpose eq27848 eq47960
    | (have j0 := eq47960 X0 X1 X2 x
       grind)
    | exact resolve eq47960 eq27848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47960
  have eq48797 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X1)) (M.op x (M.op X2 X2))) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48399 X0 X1 X2
       have i₂ := eq29689 (M.op X2 X2)
       grind)
    | exact superpose eq29689 eq48399
    | (have j0 := eq48399 X0 X1 X2
       grind)
    | exact resolve eq48399 eq29689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48399
  have eq49168 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X1)) (M.op x x)) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq48797 X0 X1 x
       have i₂ := eq27848 x x
       grind)
    | exact superpose eq27848 eq48797
    | (have j0 := eq48797 X0 X1 x
       grind)
    | exact resolve eq48797 eq27848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48797
  have eq49507 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X1)) x) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq49168 X0 X1
       have i₂ := eq27848 (σ (τ X1)) x
       grind)
    | exact superpose eq27848 eq49168
    | (have j0 := eq49168 X0 X1
       grind)
    | exact resolve eq49168 eq27848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27848 eq49168
  have eq49761 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op x (σ (τ X1))) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq49507 X0 X1
       have i₂ := eq29689 (σ (τ X1))
       grind)
    | exact superpose eq29689 eq49507
    | (have j0 := eq49507 X0 X1
       grind)
    | exact resolve eq49507 eq29689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49507
  have eq49951 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op x X1) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq49761 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq49761
    | (have j0 := eq49761 X0 X1
       grind)
    | exact resolve eq49761 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49761
  have eq50063 : ∀ X0 X1 : G, (M.op (M.op x X1) (k X0 X1)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq49951 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq49951
    | (have j0 := eq49951 X0 X1
       grind)
    | exact resolve eq49951 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49951
  have eq50122 : ∀ X0 X1 : G, (σ (τ X0)) = x ∨ (M.op (M.op x X1) (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq50063 X0 X1
       have i₂ := eq27828 (σ (τ X0))
       grind)
    | exact superpose eq27828 eq50063
    | (have j0 := eq50063 X0 X1
       grind)
    | exact resolve eq50063 eq27828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50063
  have eq50156 : ∀ X0 X1 : G, (M.op (M.op x X1) (k X0 X1)) = X0 ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq50122 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq50122
    | (have j0 := eq50122 X0 X1
       grind)
    | exact resolve eq50122 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50122
  have eq186064 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) x) ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq34163 X0
       have i₂ := eq43494 (σ X0) x
       grind)
    | exact superpose eq43494 eq34163
    | (have j1 := eq43494 (σ X0) x
       grind)
    | exact resolve eq34163 eq43494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34163 eq43494
  have eq186118 : ∀ X0 : G, (σ (k X0 x)) = (M.op x (σ X0)) ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq186064 X0
       have i₂ := eq29689 (σ X0)
       grind)
    | exact superpose eq29689 eq186064
    | (have j0 := eq186064 X0
       grind)
    | exact resolve eq186064 eq29689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29689 eq186064
  have eq186226 : ∀ X0 : G, (σ (k X0 x)) = (M.op x (σ X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq186118 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq186118
    | (have j0 := eq186118 X0
       grind)
    | exact resolve eq186118 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186118
  have eq223626 : ∀ X0 X1 X2 : G, (M.op (k (M.op X1 X1) X2) X0) = (k X0 x) ∨ x = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1008 X1 X2 x (k X0 x)
       have i₂ := eq50156 X0 x
       grind)
    | exact superpose eq50156 eq1008
    | (have j1 := eq50156 X0 X1
       grind)
    | exact resolve eq1008 eq50156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008 eq50156
  have eq223718 : ∀ X0 X2 : G, (M.op (k x X2) X0) = (k X0 x) ∨ x = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq223626 X0 x X2
       have i₂ := eq27828 x
       grind)
    | exact superpose eq27828 eq223626
    | (have j0 := eq223626 X0 x X2
       grind)
    | exact resolve eq223626 eq27828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27828 eq223626
  have eq223819 : ∀ X0 : G, (M.op x X0) = (k X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq223718 X0 x
       have i₂ := eq27154 x
       grind)
    | exact superpose eq27154 eq223718
    | (have j0 := eq223718 X0 x
       grind)
    | exact resolve eq223718 eq27154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27154 eq223718
  have eq361297 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) ∨ x = X0 ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq186226 X0
       have i₂ := eq223819 X0
       grind)
    | exact superpose eq223819 eq186226
    | (have j0 := eq186226 X0
       have j1 := eq223819 X0
       grind)
    | exact resolve eq186226 eq223819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186226 eq223819
  have eq361379 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq361297 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361297
  have eq372140 : (M.op x (σ y)) ≠ (M.op x (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq36156
       have i₂ := eq361379 y
       grind)
    | exact superpose eq361379 eq36156
    | (have j1 := eq361379 y
       grind)
    | (have r₁ := eq36156
       have r₂ := eq361379 y
       grind)
    | exact resolve eq36156 eq361379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36156 eq361379
  have eq372158 : x = y := by grind
  clear eq372140
  have eq373046 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq372158
       grind)
    | exact superpose eq372158 eq14
    | exact resolve eq14 eq372158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372158
  have eq373047 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq373046
       have i₂ := eq27887 x
       grind)
    | exact superpose eq27887 eq373046
    | exact resolve eq373046 eq27887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27887 eq373046
  have eq373049 : False := by grind
  exact eq373049

/-- `Equation695`: `x = y ◇ (x ◇ ((z ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_y_pxy_Equation695 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law695 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law695.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X2 X2) X1))) = X0 := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq17 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2))) (M.op X3 X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2))) X2
       have i₂ := eq8 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op (M.op X1 X1) X2) X0
       have i₂ := eq8 (M.op X0 X0) X2 X1
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
  have eq25 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X1 ∨ (k X0 X2) = (M.op X0 X2) := by
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
  have eq28 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq30 : ∀ X0 X1 X2 : G, (k X0 X1) = X1 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq25 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq42 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X2 (M.op X0 X0) (M.op X1 X1)
       have i₂ := eq18 X1 X0 (M.op X0 X0)
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (M.op X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X1 X1) (M.op X0 X0)
       have i₂ := eq18 X1 X0 (M.op X0 X0)
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X1 X1) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (M.op X2 X2) (M.op (M.op X1 X1) X0)) (M.op (M.op X1 X1) X0) X2
       have i₂ := eq18 (M.op (M.op X2 X2) (M.op (M.op X1 X1) X0)) X1 X0
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq73 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (k X1 X2) = (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq30 X1 (σ X0) X2
       grind)
    | exact superpose eq30 eq22
    | (have j1 := eq30 X1 X1 X2
       grind)
    | exact resolve eq22 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq79 : ∀ X0 X1 X2 : G, (k (τ X1) X0) = X0 ∨ (k X1 X2) = (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq73 X0 X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq73
    | (have j0 := eq73 X0 X1 X2
       grind)
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq102 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X3 X1)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq17 X1 (M.op X0 X0) x X3
       have i₂ := eq18 x X0 (M.op X0 X0)
       grind)
    | exact superpose eq18 eq17
    | exact resolve eq17 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op (M.op X4 X4) (M.op X5 X5))) = (M.op (M.op (M.op X0 X1) (M.op (M.op X2 X2) (M.op X3 X3))) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq17 (M.op X0 X1) X2 X3 (M.op X1 (M.op (M.op X4 X4) (M.op X5 X5)))
       have i₂ := eq17 X1 X4 X5 X0
       grind)
    | exact superpose eq17 eq17
    | exact resolve eq17 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq14
    | (have j1 := eq28 x x
       grind)
    | exact resolve eq14 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) X1
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq11
    | (have j0 := eq11 (σ X0) X1
       have j1 := eq28 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq11 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 X1 X2 X3 : G, (σ X0) = (M.op (M.op (σ X1) (M.op (M.op X2 X2) (M.op X3 X3))) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17 (σ X1) X2 X3 (σ X0)
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq17
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq17 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq217 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq28 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq197 X0 X1
       have j1 := eq11 (σ X0) X1
       grind)
    | (have r₁ := eq197 X0 X1
       have r₂ := eq11 (σ X0) X1
       grind)
    | exact resolve eq197 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq466 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 x X1 (M.op X1 X1)
       have i₂ := eq42 (M.op X1 X1) X0 x
       grind)
    | (have i₁ := eq18 (M.op X1 X1) X1 (M.op X1 X1)
       have i₂ := eq42 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq42 eq18
    | exact resolve eq18 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq587 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (M.op X2 X2) X1) X1 X2
       have i₂ := eq466 (M.op (M.op X2 X2) X1) X0
       grind)
    | (have i₁ := eq8 (M.op (M.op X2 X2) X1) X1 X2
       have i₂ := eq466 X0 (M.op (M.op X2 X2) X1)
       grind)
    | exact superpose eq466 eq8
    | exact resolve eq8 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq648 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 X3)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq18 X3 x (M.op X0 (M.op X2 X2))
       have i₂ := eq49 X2 x X0
       grind)
    | exact superpose eq49 eq18
    | exact resolve eq18 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq49
  have eq929 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op (M.op X1 X1) X0) x
       have i₂ := eq51 X0 X1 x
       grind)
    | exact superpose eq51 eq8
    | exact resolve eq8 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1040 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq102 X2 X1 X1
       have i₂ := eq466 X1 X0
       grind)
    | (have i₁ := eq102 X2 X1 X1
       have i₂ := eq466 X0 X1
       grind)
    | exact superpose eq466 eq102
    | exact resolve eq102 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq1283 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k (σ (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq221 (τ X0) X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq221
    | (have j0 := eq221 (τ X0) X1
       grind)
    | exact resolve eq221 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq1294 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k (σ (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1283 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1283
    | (have j0 := eq1283 X0 X1
       grind)
    | exact resolve eq1283 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283
  have eq1301 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1294 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1294
    | (have j0 := eq1294 X0 X1
       grind)
    | exact resolve eq1294 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294
  have eq1318 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1301 (τ X0) X1
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq1301
    | (have j0 := eq1301 (τ X0) X1
       grind)
    | exact resolve eq1301 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1301
  have eq4601 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq217 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq217
    | (have j0 := eq217 (τ X0)
       grind)
    | exact resolve eq217 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq4617 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4601 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4601
    | (have j0 := eq4601 X0
       grind)
    | exact resolve eq4601 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4601
  have eq4627 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4617 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4617
    | (have j0 := eq4617 X0
       grind)
    | exact resolve eq4617 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4617
  have eq7584 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq195
       have i₂ := eq30 x X0 y
       grind)
    | exact superpose eq30 eq195
    | (have j1 := eq30 x X0 x
       grind)
    | exact resolve eq195 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq195
  have eq7587 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7584 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7584
  have eq7694 : ∀ X0 : G, (σ (τ X0)) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x
       have i₂ := eq7587 (τ X0)
       grind)
    | exact superpose eq7587 eq16
    | exact resolve eq16 eq7587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7587
  have eq7698 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq7694 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7694
    | exact resolve eq7694 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7694
  have eq7713 : ∀ X0 : G, (k (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7698 X0
       have j1 := eq11 (σ x) X0
       grind)
    | (have r₁ := eq7698 X0
       have r₂ := eq11 (σ x) x
       grind)
    | exact resolve eq7698 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7698
  have eq7923 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k (τ (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1318 (σ x) X0
       have i₂ := eq7713 (σ x)
       grind)
    | exact superpose eq7713 eq1318
    | (have j0 := eq1318 (σ x) X0
       grind)
    | exact resolve eq1318 eq7713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7925 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4627 (σ x)
       have i₂ := eq7713 (σ x)
       grind)
    | exact superpose eq7713 eq4627
    | (have j0 := eq4627 (σ x)
       grind)
    | (have r₁ := eq4627 (σ x)
       have r₂ := eq7713 (σ x)
       grind)
    | exact resolve eq4627 eq7713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7713
  have eq7942 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq7925
  have eq7943 : ∀ X0 : G, (k (τ (σ x)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7923 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7923
  have eq7952 : ∀ X0 : G, (k x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7943 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq7943
    | exact resolve eq7943 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7943
  have eq8679 : ∀ X0 : G, (τ x) ≠ (τ x) ∨ (k (τ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1318 x X0
       have i₂ := eq7952 x
       grind)
    | exact superpose eq7952 eq1318
    | (have j0 := eq1318 x X0
       grind)
    | exact resolve eq1318 eq7952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318
  have eq8681 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4627 x
       have i₂ := eq7952 x
       grind)
    | exact superpose eq7952 eq4627
    | (have j0 := eq4627 x
       grind)
    | (have r₁ := eq4627 x
       have r₂ := eq7952 x
       grind)
    | exact resolve eq4627 eq7952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7952
  have eq8698 : x = (M.op x x) := by grind
  clear eq8681
  have eq8699 : ∀ X0 : G, (k (τ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq8679 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8679
  have eq9177 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op x X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 x
       have i₂ := eq8698
       grind)
    | exact superpose eq8698 eq8
    | exact resolve eq8 eq8698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9198 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op x X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 x X0
       have i₂ := eq8698
       grind)
    | exact superpose eq8698 eq51
    | exact resolve eq51 eq8698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq9231 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq466 X0 x
       have i₂ := eq8698
       grind)
    | exact superpose eq8698 eq466
    | exact resolve eq466 eq8698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq9234 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq587 x X1 X0
       have i₂ := eq8698
       grind)
    | exact superpose eq8698 eq587
    | exact resolve eq587 eq8698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq9237 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq648 X0 X1 x
       have i₂ := eq8698
       grind)
    | exact superpose eq8698 eq648
    | exact resolve eq648 eq8698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq9242 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1040 x X0 X1
       have i₂ := eq8698
       grind)
    | exact superpose eq8698 eq1040
    | exact resolve eq1040 eq8698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040 eq8698
  have eq9279 : ∀ X1 : G, (M.op (M.op x X1) x) = X1 := by
    intro X1
    first
    | (have i₁ := eq9198 x X1
       have i₂ := eq9234 x (M.op x X1)
       grind)
    | exact superpose eq9234 eq9198
    | exact resolve eq9198 eq9234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9198
  have eq9887 : ∀ X0 : G, x = (σ (k X0 X0)) ∨ (σ X0) = x := by
    intro X0
    first
    | (have i₁ := eq28 X0 X0
       have i₂ := eq9231 (σ X0)
       grind)
    | exact superpose eq9231 eq28
    | exact resolve eq28 eq9231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq10816 : (τ x) ≠ (τ x) ∨ (τ x) = (M.op (τ x) (τ x)) := by
    first
    | (have i₁ := eq4627 (τ x)
       have i₂ := eq8699 (τ x)
       grind)
    | exact superpose eq8699 eq4627
    | (have j0 := eq4627 (τ x)
       grind)
    | (have r₁ := eq4627 (τ x)
       have r₂ := eq8699 (τ x)
       grind)
    | exact resolve eq4627 eq8699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4627 eq8699
  have eq10834 : (τ x) = (M.op (τ x) (τ x)) := by grind
  clear eq10816
  have eq10852 : x = (τ x) := by
    first
    | (have i₁ := eq10834
       have i₂ := eq9231 (τ x)
       grind)
    | exact superpose eq9231 eq10834
    | exact resolve eq10834 eq9231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10834
  have eq11747 : x = (σ x) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq10852
       grind)
    | exact superpose eq10852 eq10
    | exact resolve eq10 eq10852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11749 : ∀ X0 : G, (k (σ X0) x) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq16 x X0
       have i₂ := eq10852
       grind)
    | exact superpose eq10852 eq16
    | exact resolve eq16 eq10852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq10852
  have eq12601 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq11747
       grind)
    | exact superpose eq11747 eq14
    | exact resolve eq14 eq11747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11747
  have eq18263 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op (M.op X1 X1) x) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq929 x X1 (M.op x X0)
       have i₂ := eq9279 X0
       grind)
    | exact superpose eq9279 eq929
    | exact resolve eq929 eq9279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929
  have eq18264 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq18263 X0 x
       have i₂ := eq9234 x x
       grind)
    | exact superpose eq9234 eq18263
    | exact resolve eq18263 eq9234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18263
  have eq18299 : ∀ X0 : G, (M.op x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq18264 X0
       have i₂ := eq9234 x X0
       grind)
    | exact superpose eq9234 eq18264
    | exact resolve eq18264 eq9234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18264
  have eq20618 : ∀ X0 : G, (M.op x (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9279 X0
       have i₂ := eq18299 (M.op x X0)
       grind)
    | exact superpose eq18299 eq9279
    | exact resolve eq9279 eq18299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9279
  have eq29011 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X3 (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2)))) = (M.op (M.op (M.op (M.op X4 X4) X3) X0) (M.op (M.op X5 X5) (M.op X6 X6))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq8 (M.op (M.op (M.op (M.op X4 X4) X3) X0) (M.op (M.op X5 X5) (M.op X6 X6))) X3 X4
       have i₂ := eq113 (M.op (M.op X4 X4) X3) X0 X5 X6 X1 X2
       grind)
    | exact superpose eq113 eq8
    | exact resolve eq8 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29040 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2)))) = (M.op (M.op (M.op (M.op X4 X4) X3) X0) (M.op (M.op X5 X5) x)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq29011 X0 X1 X2 X3 X4 X5 x
       have i₂ := eq9237 (M.op X5 X5) x
       grind)
    | exact superpose eq9237 eq29011
    | exact resolve eq29011 eq9237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29011
  have eq29686 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2)))) = (M.op (M.op (M.op (M.op X4 X4) X3) X0) (M.op x (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq29040 X0 X1 X2 X3 X4 X5
       have i₂ := eq18299 (M.op X5 X5)
       grind)
    | exact superpose eq18299 eq29040
    | exact resolve eq29040 eq18299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29040
  have eq30153 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2)))) = (M.op (M.op (M.op (M.op X4 X4) X3) X0) (M.op x x)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq29686 X0 X1 X2 X3 X4 x
       have i₂ := eq9237 x x
       grind)
    | exact superpose eq9237 eq29686
    | exact resolve eq29686 eq9237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29686
  have eq30593 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2)))) = (M.op (M.op (M.op (M.op X4 X4) X3) X0) x) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq30153 X0 X1 X2 X3 X4
       have i₂ := eq9237 (M.op (M.op (M.op X4 X4) X3) X0) x
       grind)
    | exact superpose eq9237 eq30153
    | exact resolve eq30153 eq9237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30153
  have eq31020 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2)))) = (M.op x (M.op (M.op (M.op X4 X4) X3) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq30593 X0 X1 X2 X3 X4
       have i₂ := eq18299 (M.op (M.op (M.op X4 X4) X3) X0)
       grind)
    | exact superpose eq18299 eq30593
    | exact resolve eq30593 eq18299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30593
  have eq31373 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2)))) = (M.op x (M.op (M.op X3 x) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq31020 X0 X1 X2 X3 x
       have i₂ := eq9234 x X3
       grind)
    | exact superpose eq9234 eq31020
    | exact resolve eq31020 eq9234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9234 eq31020
  have eq31663 : ∀ X0 X1 X3 : G, (M.op X3 (M.op X0 (M.op (M.op X1 X1) x))) = (M.op x (M.op (M.op X3 x) X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq31373 X0 X1 x X3
       have i₂ := eq9237 (M.op X1 X1) x
       grind)
    | exact superpose eq9237 eq31373
    | exact resolve eq31373 eq9237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31373
  have eq31899 : ∀ X0 X1 X3 : G, (M.op X3 (M.op X0 (M.op x (M.op X1 X1)))) = (M.op x (M.op (M.op X3 x) X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq31663 X0 X1 X3
       have i₂ := eq18299 (M.op X1 X1)
       grind)
    | exact superpose eq18299 eq31663
    | exact resolve eq31663 eq18299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31663
  have eq32057 : ∀ X0 X3 : G, (M.op X3 (M.op X0 (M.op x x))) = (M.op x (M.op (M.op X3 x) X0)) := by
    intro X0 X3
    first
    | (have i₁ := eq31899 X0 x X3
       have i₂ := eq9237 x x
       grind)
    | exact superpose eq9237 eq31899
    | exact resolve eq31899 eq9237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31899
  have eq32172 : ∀ X0 X3 : G, (M.op X3 (M.op X0 x)) = (M.op x (M.op (M.op X3 x) X0)) := by
    intro X0 X3
    first
    | (have i₁ := eq32057 X0 X3
       have i₂ := eq9237 X0 x
       grind)
    | exact superpose eq9237 eq32057
    | exact resolve eq32057 eq9237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32057
  have eq51762 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op (M.op X2 X2) (M.op X3 X3))) X0) x) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9242 X1 (M.op x x)
       have i₂ := eq113 X0 X1 X2 X3 x x
       grind)
    | exact superpose eq113 eq9242
    | exact resolve eq9242 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq9242
  have eq51985 : ∀ X0 X1 X2 X3 : G, (M.op x (M.op (M.op (M.op X0 X1) (M.op (M.op X2 X2) (M.op X3 X3))) X0)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51762 X0 X1 X2 X3
       have i₂ := eq18299 (M.op (M.op (M.op X0 X1) (M.op (M.op X2 X2) (M.op X3 X3))) X0)
       grind)
    | exact superpose eq18299 eq51762
    | exact resolve eq51762 eq18299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51762
  have eq52084 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op (M.op X0 X1) (M.op (M.op X2 X2) x)) X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51985 X0 X1 X2 x
       have i₂ := eq9237 (M.op X2 X2) x
       grind)
    | exact superpose eq9237 eq51985
    | exact resolve eq51985 eq9237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51985
  have eq52144 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op (M.op X0 X1) (M.op x (M.op X2 X2))) X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52084 X0 X1 X2
       have i₂ := eq18299 (M.op X2 X2)
       grind)
    | exact superpose eq18299 eq52084
    | exact resolve eq52084 eq18299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52084
  have eq52153 : ∀ X0 X1 : G, (M.op x (M.op (M.op (M.op X0 X1) (M.op x x)) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52144 X0 X1 x
       have i₂ := eq9237 x x
       grind)
    | exact superpose eq9237 eq52144
    | exact resolve eq52144 eq9237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52144
  have eq52158 : ∀ X0 X1 : G, (M.op x (M.op (M.op (M.op X0 X1) x) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52153 X0 X1
       have i₂ := eq9237 (M.op X0 X1) x
       grind)
    | exact superpose eq9237 eq52153
    | exact resolve eq52153 eq9237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52153
  have eq52163 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52158 X0 X1
       have i₂ := eq32172 X0 (M.op X0 X1)
       grind)
    | exact superpose eq32172 eq52158
    | exact resolve eq52158 eq32172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52158
  have eq64132 : ∀ X0 X1 X2 X3 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X1)) (M.op (M.op X2 X2) (M.op X3 X3))) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq206 (τ X0) (τ X1) X2 X3
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq206
    | (have j0 := eq206 (τ X0) X1 X2 X3
       grind)
    | exact resolve eq206 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq206
  have eq64578 : ∀ X0 X1 X2 X3 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X1)) (M.op (M.op X2 X2) (M.op X3 X3))) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64132 X0 X1 X2 X3
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq64132
    | (have j0 := eq64132 X0 X1 X2 X3
       grind)
    | exact resolve eq64132 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64132
  have eq65012 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X1)) (M.op (M.op X2 X2) x)) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64578 X0 X1 X2 x
       have i₂ := eq9237 (M.op X2 X2) x
       grind)
    | exact superpose eq9237 eq64578
    | (have j0 := eq64578 X0 X1 X2 x
       grind)
    | exact resolve eq64578 eq9237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64578
  have eq65408 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X1)) (M.op x (M.op X2 X2))) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65012 X0 X1 X2
       have i₂ := eq18299 (M.op X2 X2)
       grind)
    | exact superpose eq18299 eq65012
    | (have j0 := eq65012 X0 X1 X2
       grind)
    | exact resolve eq65012 eq18299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65012
  have eq65761 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X1)) (M.op x x)) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq65408 X0 X1 x
       have i₂ := eq9237 x x
       grind)
    | exact superpose eq9237 eq65408
    | (have j0 := eq65408 X0 X1 x
       grind)
    | exact resolve eq65408 eq9237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65408
  have eq66071 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X1)) x) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq65761 X0 X1
       have i₂ := eq9237 (σ (τ X1)) x
       grind)
    | exact superpose eq9237 eq65761
    | (have j0 := eq65761 X0 X1
       grind)
    | exact resolve eq65761 eq9237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9237 eq65761
  have eq66304 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op x (σ (τ X1))) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq66071 X0 X1
       have i₂ := eq18299 (σ (τ X1))
       grind)
    | exact superpose eq18299 eq66071
    | (have j0 := eq66071 X0 X1
       grind)
    | exact resolve eq66071 eq18299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66071
  have eq66468 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op x X1) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq66304 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq66304
    | (have j0 := eq66304 X0 X1
       grind)
    | exact resolve eq66304 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66304
  have eq66563 : ∀ X0 X1 : G, (M.op (M.op x X1) (k X0 X1)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq66468 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq66468
    | (have j0 := eq66468 X0 X1
       grind)
    | exact resolve eq66468 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66468
  have eq66626 : ∀ X0 X1 : G, (σ (τ X0)) = x ∨ (M.op (M.op x X1) (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq66563 X0 X1
       have i₂ := eq9231 (σ (τ X0))
       grind)
    | exact superpose eq9231 eq66563
    | (have j0 := eq66563 X0 X1
       grind)
    | exact resolve eq66563 eq9231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66563
  have eq66664 : ∀ X0 X1 : G, (M.op (M.op x X1) (k X0 X1)) = X0 ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq66626 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq66626
    | (have j0 := eq66626 X0 X1
       grind)
    | exact resolve eq66626 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66626
  have eq72006 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op X0 (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq52163 X1 (M.op X0 (M.op x X1))
       have i₂ := eq9177 X1 X0
       grind)
    | exact superpose eq9177 eq52163
    | exact resolve eq52163 eq9177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9177 eq52163
  have eq95716 : ∀ X0 : G, x = (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq15 X0 (τ X0)
       have i₂ := eq9887 (τ X0)
       grind)
    | exact superpose eq9887 eq15
    | (have j1 := eq9887 (τ X0)
       grind)
    | exact resolve eq15 eq9887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq9887
  have eq95849 : ∀ X0 : G, x = (k X0 X0) ∨ (σ (τ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq95716 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq95716
    | (have j0 := eq95716 X0
       grind)
    | exact resolve eq95716 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95716
  have eq95931 : ∀ X0 : G, x = (k X0 X0) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq95849 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq95849
    | (have j0 := eq95849 X0
       grind)
    | exact resolve eq95849 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95849
  have eq97407 : ∀ X0 X1 : G, (τ X0) = x ∨ (k X0 X1) = (M.op X0 X1) ∨ (τ X0) = x := by
    intro X0 X1
    first
    | (have i₁ := eq79 (τ X0) X0 X1
       have i₂ := eq95931 (τ X0)
       grind)
    | exact superpose eq95931 eq79
    | (have j0 := eq79 X0 X0 X1
       have j1 := eq95931 (τ X0)
       grind)
    | exact resolve eq79 eq95931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq95931
  have eq97428 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (τ X0) = x := by
    intro X0 X1
    first
    | (have j0 := eq97407 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97407
  have eq158181 : ∀ X0 : G, (M.op (σ X0) x) = (σ (k X0 x)) ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq11749 X0
       have i₂ := eq97428 (σ X0) x
       grind)
    | exact superpose eq97428 eq11749
    | (have j1 := eq97428 (σ X0) x
       grind)
    | exact resolve eq11749 eq97428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11749 eq97428
  have eq158271 : ∀ X0 : G, (σ (k X0 x)) = (M.op x (σ X0)) ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq158181 X0
       have i₂ := eq18299 (σ X0)
       grind)
    | exact superpose eq18299 eq158181
    | (have j0 := eq158181 X0
       grind)
    | exact resolve eq158181 eq18299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18299 eq158181
  have eq158374 : ∀ X0 : G, (σ (k X0 x)) = (M.op x (σ X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq158271 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq158271
    | (have j0 := eq158271 X0
       grind)
    | exact resolve eq158271 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158271
  have eq187773 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op (k X0 x) x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq32172 (k X0 x) x
       have i₂ := eq66664 X0 x
       grind)
    | exact superpose eq66664 eq32172
    | (have j1 := eq66664 X0 x
       grind)
    | exact resolve eq32172 eq66664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32172 eq66664
  have eq187861 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op x (k X0 x))) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq187773 X0
       have i₂ := eq72006 x (k X0 x)
       grind)
    | exact superpose eq72006 eq187773
    | (have j0 := eq187773 X0
       grind)
    | exact resolve eq187773 eq72006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72006 eq187773
  have eq187967 : ∀ X0 : G, (M.op x X0) = (k X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq187861 X0
       have i₂ := eq20618 (k X0 x)
       grind)
    | exact superpose eq20618 eq187861
    | (have j0 := eq187861 X0
       grind)
    | exact resolve eq187861 eq20618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20618 eq187861
  have eq342342 : ∀ X0 : G, (σ (M.op x X0)) = (M.op x (σ X0)) ∨ x = X0 ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq158374 X0
       have i₂ := eq187967 X0
       grind)
    | exact superpose eq187967 eq158374
    | (have j0 := eq158374 X0
       have j1 := eq187967 X0
       grind)
    | exact resolve eq158374 eq187967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158374 eq187967
  have eq342552 : ∀ X0 : G, (σ (M.op x X0)) = (M.op x (σ X0)) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq342342 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342342
  have eq373228 : (M.op x (σ y)) ≠ (M.op x (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq12601
       have i₂ := eq342552 y
       grind)
    | exact superpose eq342552 eq12601
    | (have j1 := eq342552 y
       grind)
    | (have r₁ := eq12601
       have r₂ := eq342552 y
       grind)
    | exact resolve eq12601 eq342552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12601 eq342552
  have eq373344 : x = y := by grind
  clear eq373228
  have eq376562 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq373344
       grind)
    | exact superpose eq373344 eq14
    | exact resolve eq14 eq373344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373344
  have eq376563 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq376562
       have i₂ := eq9231 x
       grind)
    | exact superpose eq9231 eq376562
    | exact resolve eq376562 eq9231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9231 eq376562
  have eq376565 : False := by grind
  exact eq376565

/-- `Equation695`: `x = y ◇ (x ◇ ((z ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation695 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law695 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law695.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X2 X2) X1))) = X0 := by
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
  have eq19 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op (M.op X1 X1) X2) X0
       have i₂ := eq8 (M.op X0 X0) X2 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq32 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 := by
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
  have eq34 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  clear eq17
  have eq44 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X2 (M.op X0 X0) (M.op X1 X1)
       have i₂ := eq19 X1 X0 (M.op X0 X0)
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (M.op X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X1 X1) (M.op X0 X0)
       have i₂ := eq19 X1 X0 (M.op X0 X0)
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X1 X1) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (M.op X2 X2) (M.op (M.op X1 X1) X0)) (M.op (M.op X1 X1) X0) X2
       have i₂ := eq19 (M.op (M.op X2 X2) (M.op (M.op X1 X1) X0)) X1 X0
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 x X1 (M.op X1 X1)
       have i₂ := eq44 (M.op X1 X1) X0 x
       grind)
    | (have i₁ := eq19 (M.op X1 X1) X1 (M.op X1 X1)
       have i₂ := eq44 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq44 eq19
    | exact resolve eq19 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    grind
  clear eq44
  have eq286 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq300 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq378 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq386 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (M.op X2 X2) X1) X1 X2
       have i₂ := eq235 (M.op (M.op X2 X2) X1) X0
       grind)
    | (have i₁ := eq8 (M.op (M.op X2 X2) X1) X1 X2
       have i₂ := eq235 X0 (M.op (M.op X2 X2) X1)
       grind)
    | exact superpose eq235 eq8
    | exact resolve eq8 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq235 (σ X0) X1
       grind)
    | (have i₁ := eq31 X0 X0
       have i₂ := eq235 X0 (σ X0)
       grind)
    | exact superpose eq235 eq31
    | exact resolve eq31 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq235
  have eq471 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1 (M.op X0 X0)
       have i₂ := eq378 X0 (σ X1)
       grind)
    | exact superpose eq378 eq39
    | exact resolve eq39 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0)
       have i₂ := eq378 X0 (τ X1)
       grind)
    | exact superpose eq378 eq16
    | exact resolve eq16 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq553 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 X3)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq19 X3 x (M.op X0 (M.op X2 X2))
       have i₂ := eq51 X2 x X0
       grind)
    | exact superpose eq51 eq19
    | exact resolve eq19 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq51
  have eq2449 : ∀ X0 X1 : G, (τ (τ (M.op X0 X0))) = (k X1 (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1 (τ (M.op X0 X0))
       have i₂ := eq471 X0 (σ X1)
       grind)
    | exact superpose eq471 eq39
    | exact resolve eq39 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq471
  have eq2725 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (k X1 (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (σ (M.op X0 X0))
       have i₂ := eq472 X0 (τ X1)
       grind)
    | exact superpose eq472 eq16
    | exact resolve eq16 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3641 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq3793 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3641 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq3641
    | (have j0 := eq3641 X0 X1
       grind)
    | exact resolve eq3641 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3641
  have eq5945 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq392 X1 (σ (M.op X0 X0))
       have i₂ := eq472 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq472 eq392
    | (have j0 := eq392 X1 (σ (M.op X0 X0))
       grind)
    | exact resolve eq392 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq5946 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (σ (M.op X0 X0)))) ∨ (M.op X1 X1) = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq392 X1 (σ (σ (M.op X0 X0)))
       have i₂ := eq2725 X0 (σ (σ (M.op X0 X0)))
       grind)
    | exact superpose eq2725 eq392
    | (have j0 := eq392 X1 (σ (σ (M.op X0 X0)))
       grind)
    | exact resolve eq392 eq2725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725
  have eq5948 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) ∨ (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq392 X1 (τ (τ (M.op X0 X0)))
       have i₂ := eq2449 X0 (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq2449 eq392
    | (have j0 := eq392 X1 (τ (τ (M.op X0 X0)))
       grind)
    | exact resolve eq392 eq2449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2449
  have eq5949 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq392 X1 (M.op X0 X0)
       have i₂ := eq247 X0 X0
       grind)
    | exact superpose eq247 eq392
    | (have j0 := eq392 X1 (M.op X0 X0)
       grind)
    | exact resolve eq392 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq392
  have eq6107 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq5949 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5949
  have eq6108 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq5948 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5948
  have eq6110 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq5946 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5946
  have eq6111 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq5945 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5945
  have eq6147 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6108 X0 X1
       have i₂ := eq10 (τ (M.op X0 X0))
       grind)
    | exact superpose eq10 eq6108
    | exact resolve eq6108 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6108
  have eq6346 : ∀ X0 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq6107 X2 x
       have i₂ := eq6107 X0 x
       grind)
    | exact superpose eq6107 eq6107
    | exact resolve eq6107 eq6107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6727 : ∀ X0 X2 : G, (τ (M.op X0 X0)) = (τ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq6147 X2 x
       have i₂ := eq6147 X0 x
       grind)
    | exact superpose eq6147 eq6147
    | exact resolve eq6147 eq6147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6766 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6147 x X1
       have i₂ := eq6147 X0 x
       grind)
    | exact superpose eq6147 eq6147
    | exact resolve eq6147 eq6147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6854 : ∀ X0 X2 : G, (τ (M.op X0 X0)) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq6107 X2 x
       have i₂ := eq6147 X0 x
       grind)
    | exact superpose eq6147 eq6107
    | exact resolve eq6107 eq6147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6865 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (M.op X2 X2) X1) X1 X2
       have i₂ := eq6147 X0 (M.op (M.op X2 X2) X1)
       grind)
    | exact superpose eq6147 eq8
    | exact resolve eq8 eq6147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6900 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X1 X1) X1
       have i₂ := eq6147 X0 (M.op X1 X1)
       grind)
    | exact superpose eq6147 eq8
    | exact resolve eq8 eq6147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7355 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq286
       have i₂ := eq3793 y x
       grind)
    | exact superpose eq3793 eq286
    | (have j1 := eq3793 (σ y) (σ x)
       grind)
    | (have r₁ := eq286
       have r₂ := eq3793 y x
       grind)
    | exact resolve eq286 eq3793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286 eq3793
  have eq7356 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq7355
  have eq7427 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6346 X1 x
       have i₂ := eq6111 X0 x
       grind)
    | exact superpose eq6111 eq6346
    | exact resolve eq6346 eq6111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6346
  have eq8365 : ∀ X0 X2 : G, (τ (τ (M.op X0 X0))) = (τ (τ (M.op X2 X2))) := by
    intro X0 X2
    first
    | (have i₁ := eq6766 X2 x
       have i₂ := eq6766 X0 x
       grind)
    | exact superpose eq6766 eq6766
    | exact resolve eq6766 eq6766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8502 : ∀ X0 X2 : G, (τ (τ (M.op X0 X0))) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq6107 X2 x
       have i₂ := eq6766 X0 x
       grind)
    | exact superpose eq6766 eq6107
    | exact resolve eq6107 eq6766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8505 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6147 x X1
       have i₂ := eq6766 X0 x
       grind)
    | exact superpose eq6766 eq6147
    | exact resolve eq6147 eq6766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8510 : ∀ X0 X2 : G, (τ (M.op X2 X2)) = (τ (τ (τ (M.op X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq6727 x X2
       have i₂ := eq6766 X0 x
       grind)
    | exact superpose eq6766 eq6727
    | exact resolve eq6727 eq6766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6727 eq6766
  have eq8877 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6854 X1 x
       have i₂ := eq6111 X0 x
       grind)
    | exact superpose eq6111 eq6854
    | exact resolve eq6854 eq6111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6854
  have eq88511 : ∀ X0 : G, (M.op X0 X0) = (τ (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq6147 (σ x) X0
       have i₂ := eq7356
       grind)
    | exact superpose eq7356 eq6147
    | exact resolve eq6147 eq7356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7356
  have eq88682 : ∀ X0 : G, (M.op X0 X0) = y ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq88511 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq88511
    | exact resolve eq88511 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88511
  have eq90596 : y ≠ y ∨ y = (M.op x x) := by
    first
    | (have j0 := eq88682 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88682
  have eq90597 : y = (M.op x x) := by grind
  clear eq90596
  have eq91165 : ∀ X0 X1 : G, (M.op y (M.op (M.op X0 X0) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1 X0 x
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq53
    | exact resolve eq53 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq91201 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq386 x X1 X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq386
    | exact resolve eq386 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq91207 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq553 X0 X1 x
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq553
    | exact resolve eq553 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq91215 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq6107 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq6107
    | exact resolve eq6107 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6107
  have eq91216 : ∀ X0 : G, (M.op X0 X0) = (σ (σ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq6110 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq6110
    | exact resolve eq6110 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6110
  have eq91217 : ∀ X0 : G, (M.op X0 X0) = (σ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq6111 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq6111
    | exact resolve eq6111 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6111
  have eq91218 : ∀ X0 : G, (M.op X0 X0) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq6147 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq6147
    | exact resolve eq6147 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6147
  have eq91272 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X1 (τ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq6865 x X1 X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq6865
    | exact resolve eq6865 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6865
  have eq91297 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (σ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq7427 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq7427
    | exact resolve eq7427 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7427
  have eq91300 : ∀ X0 : G, (τ (τ (M.op X0 X0))) = (τ (τ y)) := by
    intro X0
    first
    | (have i₁ := eq8365 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq8365
    | exact resolve eq8365 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8365
  have eq91302 : ∀ X0 : G, (σ (M.op X0 X0)) = (τ (τ y)) := by
    intro X0
    first
    | (have i₁ := eq8502 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq8502
    | exact resolve eq8502 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8502
  have eq91304 : ∀ X0 : G, (M.op X0 X0) = (τ (τ (τ y))) := by
    intro X0
    first
    | (have i₁ := eq8505 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq8505
    | exact resolve eq8505 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8505
  have eq91305 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (τ (τ y))) := by
    intro X0
    first
    | (have i₁ := eq8510 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq8510
    | exact resolve eq8510 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8510
  have eq91308 : ∀ X0 : G, (τ (M.op X0 X0)) = (σ (σ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq8877 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq8877
    | exact resolve eq8877 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8877 eq90597
  have eq91332 : (σ (σ (σ y))) = (τ (τ (τ y))) := by
    first
    | (have i₁ := eq91305 x
       have i₂ := eq91308 x
       grind)
    | exact superpose eq91308 eq91305
    | exact resolve eq91305 eq91308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91305
  have eq91333 : (τ (τ y)) = (τ (σ (σ (σ y)))) := by
    first
    | (have i₁ := eq91300 x
       have i₂ := eq91308 x
       grind)
    | exact superpose eq91308 eq91300
    | exact resolve eq91300 eq91308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91300
  have eq91335 : (σ (σ (σ y))) = (τ (τ y)) := by
    first
    | (have i₁ := eq91297 x
       have i₂ := eq91302 x
       grind)
    | exact superpose eq91302 eq91297
    | exact resolve eq91297 eq91302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91297
  have eq91380 : (σ (σ y)) = (τ y) := by
    first
    | (have i₁ := eq91217 x
       have i₂ := eq91218 x
       grind)
    | exact superpose eq91218 eq91217
    | exact resolve eq91217 eq91218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91217
  have eq91381 : (σ (σ (σ y))) = (τ y) := by
    first
    | (have i₁ := eq91216 x
       have i₂ := eq91218 x
       grind)
    | exact superpose eq91218 eq91216
    | exact resolve eq91216 eq91218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91216
  have eq91385 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (τ y)) := by
    intro X0
    first
    | (have i₁ := eq91207 X0 x
       have i₂ := eq91218 x
       grind)
    | exact superpose eq91218 eq91207
    | exact resolve eq91207 eq91218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91207
  have eq91387 : ∀ X1 : G, (M.op X1 y) = (M.op (τ y) X1) := by
    intro X1
    first
    | (have i₁ := eq91201 x X1
       have i₂ := eq91218 x
       grind)
    | exact superpose eq91218 eq91201
    | exact resolve eq91201 eq91218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91201
  have eq91413 : ∀ X1 : G, (M.op y (M.op X1 (τ y))) = X1 := by
    intro X1
    first
    | (have i₁ := eq91165 x X1
       have i₂ := eq91272 x X1
       grind)
    | exact superpose eq91272 eq91165
    | exact resolve eq91165 eq91272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91165
  have eq91427 : (σ (σ y)) = (τ (τ y)) := by
    first
    | (have i₁ := eq91333
       have i₂ := eq9 (σ (σ y))
       grind)
    | exact superpose eq9 eq91333
    | exact resolve eq91333 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91333
  have eq91453 : (τ y) = (σ (τ y)) := by
    first
    | (have i₁ := eq91381
       have i₂ := eq91380
       grind)
    | exact superpose eq91380 eq91381
    | exact resolve eq91381 eq91380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91381
  have eq91478 : ∀ X1 : G, (M.op y (M.op X1 y)) = X1 := by
    intro X1
    first
    | (have i₁ := eq91413 X1
       have i₂ := eq91385 X1
       grind)
    | exact superpose eq91385 eq91413
    | exact resolve eq91413 eq91385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91413
  have eq91488 : (τ y) = (τ (τ y)) := by
    first
    | (have i₁ := eq91427
       have i₂ := eq91380
       grind)
    | exact superpose eq91380 eq91427
    | exact resolve eq91427 eq91380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91380 eq91427
  have eq91502 : y = (τ y) := by
    first
    | (have i₁ := eq91453
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq91453
    | exact resolve eq91453 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91453
  have eq92197 : y = (σ y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq91502
       grind)
    | exact superpose eq91502 eq10
    | exact resolve eq10 eq91502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92198 : ∀ X0 : G, (σ (k y X0)) = (k y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16 y X0
       have i₂ := eq91502
       grind)
    | exact superpose eq91502 eq16
    | exact resolve eq16 eq91502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq92790 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq92197
       grind)
    | exact superpose eq92197 eq14
    | exact resolve eq14 eq92197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92812 : ∀ X0 : G, (τ (M.op y y)) = X0 ∨ (σ (k y X0)) = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq300 y x
       have i₂ := eq92197
       grind)
    | exact superpose eq92197 eq300
    | exact resolve eq300 eq92197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq92813 : ∀ X0 : G, (σ (σ (σ y))) = X0 ∨ (σ (k y X0)) = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq92812 X0
       have i₂ := eq91308 y
       grind)
    | exact superpose eq91308 eq92812
    | (have j0 := eq92812 X0
       grind)
    | exact resolve eq92812 eq91308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91308 eq92812
  have eq92824 : ∀ X0 : G, (τ (τ y)) = X0 ∨ (σ (k y X0)) = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq92813 X0
       have i₂ := eq91335
       grind)
    | exact superpose eq91335 eq92813
    | (have j0 := eq92813 X0
       grind)
    | exact resolve eq92813 eq91335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92813
  have eq92835 : ∀ X0 : G, (τ y) = X0 ∨ (σ (k y X0)) = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq92824 X0
       have i₂ := eq91488
       grind)
    | exact superpose eq91488 eq92824
    | (have j0 := eq92824 X0
       grind)
    | exact resolve eq92824 eq91488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92824
  have eq92839 : ∀ X0 : G, (σ (k y X0)) = (M.op y (σ X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq92835 X0
       have i₂ := eq91502
       grind)
    | exact superpose eq91502 eq92835
    | (have j0 := eq92835 X0
       grind)
    | exact resolve eq92835 eq91502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92835
  have eq96559 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 (τ (σ y)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6900 x X0 X1
       have i₂ := eq91215 x
       grind)
    | exact superpose eq91215 eq6900
    | exact resolve eq6900 eq91215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6900 eq91215
  have eq96990 : ∀ X1 : G, (M.op (M.op X1 (τ (σ y))) (τ y)) = X1 := by
    intro X1
    first
    | (have i₁ := eq96559 x X1
       have i₂ := eq91272 x (M.op X1 (τ (σ y)))
       grind)
    | exact superpose eq91272 eq96559
    | exact resolve eq96559 eq91272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91272 eq96559
  have eq97367 : ∀ X1 : G, (M.op (M.op X1 (τ (σ y))) y) = X1 := by
    intro X1
    first
    | (have i₁ := eq96990 X1
       have i₂ := eq91385 (M.op X1 (τ (σ y)))
       grind)
    | exact superpose eq91385 eq96990
    | exact resolve eq96990 eq91385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91385 eq96990
  have eq97677 : ∀ X1 : G, (M.op (M.op X1 y) y) = X1 := by
    intro X1
    first
    | (have i₁ := eq97367 X1
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq97367
    | exact resolve eq97367 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97367
  have eq109143 : ∀ X0 : G, (M.op y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq91478 (M.op X0 y)
       have i₂ := eq97677 X0
       grind)
    | exact superpose eq97677 eq91478
    | exact resolve eq91478 eq97677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91478 eq97677
  have eq120277 : ∀ X0 : G, (σ (M.op X0 y)) = (k y (σ X0)) ∨ (M.op (τ y) (τ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq32 y X0
       have i₂ := eq91387 X0
       grind)
    | exact superpose eq91387 eq32
    | (have j0 := eq32 y X0
       grind)
    | exact resolve eq32 eq91387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq91387
  have eq120856 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ (M.op (τ y) (τ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq120277 X0
       have i₂ := eq92198 X0
       grind)
    | exact superpose eq92198 eq120277
    | (have j0 := eq120277 X0
       grind)
    | exact resolve eq120277 eq92198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92198 eq120277
  have eq121161 : ∀ X0 : G, (τ (τ (τ y))) = X0 ∨ (σ (k y X0)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq120856 X0
       have i₂ := eq91304 (τ y)
       grind)
    | exact superpose eq91304 eq120856
    | (have j0 := eq120856 X0
       grind)
    | exact resolve eq120856 eq91304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91304 eq120856
  have eq121297 : ∀ X0 : G, (σ (σ (σ y))) = X0 ∨ (σ (k y X0)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq121161 X0
       have i₂ := eq91332
       grind)
    | exact superpose eq91332 eq121161
    | (have j0 := eq121161 X0
       grind)
    | exact resolve eq121161 eq91332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91332 eq121161
  have eq121402 : ∀ X0 : G, (τ (τ y)) = X0 ∨ (σ (k y X0)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq121297 X0
       have i₂ := eq91335
       grind)
    | exact superpose eq91335 eq121297
    | (have j0 := eq121297 X0
       grind)
    | exact resolve eq121297 eq91335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91335 eq121297
  have eq121469 : ∀ X0 : G, (τ y) = X0 ∨ (σ (k y X0)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq121402 X0
       have i₂ := eq91488
       grind)
    | exact superpose eq91488 eq121402
    | (have j0 := eq121402 X0
       grind)
    | exact resolve eq121402 eq91488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121402
  have eq121527 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq121469 X0
       have i₂ := eq91502
       grind)
    | exact superpose eq91502 eq121469
    | (have j0 := eq121469 X0
       grind)
    | exact resolve eq121469 eq91502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121469
  have eq295331 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op y (σ X0)) ∨ y = X0 ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq121527 X0
       have i₂ := eq92839 X0
       grind)
    | exact superpose eq92839 eq121527
    | (have j0 := eq121527 X0
       have j1 := eq92839 X0
       grind)
    | exact resolve eq121527 eq92839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92839 eq121527
  have eq295341 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op y (σ X0)) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq295331 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295331
  have eq301791 : (M.op (σ x) y) ≠ (M.op y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq92790
       have i₂ := eq295341 x
       grind)
    | exact superpose eq295341 eq92790
    | (have j1 := eq295341 x
       grind)
    | exact resolve eq92790 eq295341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295341
  have eq301797 : (M.op y (σ x)) ≠ (M.op y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq301791
       have i₂ := eq109143 (σ x)
       grind)
    | exact superpose eq109143 eq301791
    | (have r₁ := eq301791
       have r₂ := eq109143 (σ x)
       grind)
    | exact resolve eq301791 eq109143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301791
  have eq301798 : x = y := by grind
  clear eq301797
  have eq301971 : x = (σ x) := by
    first
    | (have i₁ := eq92197
       have i₂ := eq301798
       grind)
    | exact superpose eq301798 eq92197
    | exact resolve eq92197 eq301798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92197
  have eq301975 : (σ (M.op x x)) ≠ (M.op (σ x) x) := by
    first
    | (have i₁ := eq92790
       have i₂ := eq301798
       grind)
    | exact superpose eq301798 eq92790
    | exact resolve eq92790 eq301798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92790
  have eq301985 : ∀ X0 : G, (M.op x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq109143 X0
       have i₂ := eq301798
       grind)
    | exact superpose eq301798 eq109143
    | exact resolve eq109143 eq301798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109143 eq301798
  have eq302096 : (σ (M.op x x)) ≠ (M.op x (σ x)) := by
    first
    | (have i₁ := eq301975
       have i₂ := eq301985 (σ x)
       grind)
    | exact superpose eq301985 eq301975
    | exact resolve eq301975 eq301985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301975 eq301985
  have eq302197 : (M.op x x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq302096
       have i₂ := eq301971
       grind)
    | exact superpose eq301971 eq302096
    | exact resolve eq302096 eq301971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301971 eq302096
  have eq302267 : (M.op x x) ≠ (τ (τ y)) := by
    first
    | (have i₁ := eq302197
       have i₂ := eq91302 x
       grind)
    | exact superpose eq91302 eq302197
    | exact resolve eq302197 eq91302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91302 eq302197
  have eq302310 : (M.op x x) ≠ (τ y) := by
    first
    | (have i₁ := eq302267
       have i₂ := eq91488
       grind)
    | exact superpose eq91488 eq302267
    | exact resolve eq302267 eq91488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91488 eq302267
  have eq302337 : y ≠ (M.op x x) := by
    first
    | (have i₁ := eq302310
       have i₂ := eq91502
       grind)
    | exact superpose eq91502 eq302310
    | exact resolve eq302310 eq91502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302310
  have eq302357 : y ≠ (τ y) := by
    first
    | (have i₁ := eq302337
       have i₂ := eq91218 x
       grind)
    | exact superpose eq91218 eq302337
    | exact resolve eq302337 eq91218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91218 eq302337
  have eq302367 : y ≠ y := by
    first
    | (have i₁ := eq302357
       have i₂ := eq91502
       grind)
    | exact superpose eq91502 eq302357
    | (have r₁ := eq302357
       have r₂ := eq91502
       grind)
    | exact resolve eq302357 eq91502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91502 eq302357
  have eq302368 : False := by grind
  exact eq302368

/-- `Equation695`: `x = y ◇ (x ◇ ((z ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation695 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law695 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law695.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X2 X2) X1))) = X0 := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2))) (M.op X3 X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2))) X2
       have i₂ := eq8 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op (M.op X1 X1) X2) X0
       have i₂ := eq8 (M.op X0 X0) X2 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
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
  have eq45 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X2 (M.op X0 X0) (M.op X1 X1)
       have i₂ := eq19 X1 X0 (M.op X0 X0)
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 X2) (M.op X1 X1))) = (M.op X0 (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X3 X1 (M.op X0 (M.op (M.op X2 X2) (M.op X1 X1)))
       have i₂ := eq8 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (M.op X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X1 X1) (M.op X0 X0)
       have i₂ := eq19 X1 X0 (M.op X0 X0)
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (M.op X1 X1) X0) (M.op X2 X2) X2
       have i₂ := eq19 (M.op X2 X2) X1 X0
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X1 X1) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (M.op X2 X2) (M.op (M.op X1 X1) X0)) (M.op (M.op X1 X1) X0) X2
       have i₂ := eq19 (M.op (M.op X2 X2) (M.op (M.op X1 X1) X0)) X1 X0
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq99 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X3 X1)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq18 X1 (M.op X0 X0) x X3
       have i₂ := eq19 x X0 (M.op X0 X0)
       grind)
    | exact superpose eq19 eq18
    | exact resolve eq18 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op (M.op X4 X4) (M.op X5 X5))) = (M.op (M.op (M.op X0 X1) (M.op (M.op X2 X2) (M.op X3 X3))) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq18 (M.op X0 X1) X2 X3 (M.op X1 (M.op (M.op X4 X4) (M.op X5 X5)))
       have i₂ := eq18 X1 X4 X5 X0
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = X2 ∨ (k (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1))) X2) = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1))) X2
       have i₂ := eq18 (M.op (M.op X0 X0) (M.op X1 X1)) X0 X1 (M.op (M.op X0 X0) (M.op X1 X1))
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1))) X2
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X2) X3) (M.op (M.op X0 X0) (M.op X1 X1))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1))) X2 X3
       have i₂ := eq18 (M.op (M.op X0 X0) (M.op X1 X1)) X0 X1 (M.op (M.op X0 X0) (M.op X1 X1))
       grind)
    | exact superpose eq18 eq19
    | exact resolve eq19 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq123 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (k (M.op X1 X1) X2) ∨ (M.op (M.op X0 X0) (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq118 X0 X1 X2
       have i₂ := eq120 X0 X1 X0 (M.op X1 X1)
       grind)
    | exact superpose eq120 eq118
    | (have j0 := eq118 X0 X1 X2
       grind)
    | exact resolve eq118 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq120
  have eq133 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq40
  have eq147 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq133 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq133
    | exact resolve eq133 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq248 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq251 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq259 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq9
    | (have j1 := eq32 X0 X1
       grind)
    | exact resolve eq9 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq32 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq285 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq251 X0
       have i₂ := eq13 X0 (k X0 X0)
       grind)
    | exact superpose eq13 eq251
    | (have j0 := eq251 X0
       grind)
    | exact resolve eq251 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq411 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 x X1 (M.op X1 X1)
       have i₂ := eq45 (M.op X1 X1) X0 x
       grind)
    | (have i₁ := eq19 (M.op X1 X1) X1 (M.op X1 X1)
       have i₂ := eq45 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq45 eq19
    | exact resolve eq19 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq519 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X2 ∨ (k X1 X2) = (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq411 X1 X0
       grind)
    | (have i₁ := eq12 X1 X2
       have i₂ := eq411 X0 X1
       grind)
    | exact superpose eq411 eq12
    | (have j0 := eq12 X0 X2
       grind)
    | exact resolve eq12 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (M.op X2 X2) X1) X1 X2
       have i₂ := eq411 (M.op (M.op X2 X2) X1) X0
       grind)
    | (have i₁ := eq8 (M.op (M.op X2 X2) X1) X1 X2
       have i₂ := eq411 X0 (M.op (M.op X2 X2) X1)
       grind)
    | exact superpose eq411 eq8
    | exact resolve eq8 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq73 X1 X1
       have i₂ := eq411 X1 X0
       grind)
    | (have i₁ := eq73 X1 X1
       have i₂ := eq411 X0 X1
       grind)
    | exact superpose eq411 eq73
    | (have j0 := eq73 X1 X1
       grind)
    | (have r₁ := eq73 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq411 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq73 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq411 X0 (M.op X0 X0)
       grind)
    | exact resolve eq73 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : ∀ X0 X1 : G, (k X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq147 X1
       have i₂ := eq411 (σ X1) X0
       grind)
    | (have i₁ := eq147 X1
       have i₂ := eq411 X0 (σ X1)
       grind)
    | exact superpose eq411 eq147
    | exact resolve eq147 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq592 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 X3)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq19 X3 x (M.op X0 (M.op X2 X2))
       have i₂ := eq52 X2 x X0
       grind)
    | exact superpose eq52 eq19
    | exact resolve eq19 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq52
  have eq846 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 X3 (M.op X1 X1) X2
       have i₂ := eq53 (M.op X1 X1) X0 X1
       grind)
    | (have i₁ := eq54 X3 (M.op X1 X1) X2
       have i₂ := eq53 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq886 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op (M.op X1 X1) X0) x
       have i₂ := eq54 X0 X1 x
       grind)
    | exact superpose eq54 eq8
    | exact resolve eq8 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq989 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq99 X2 X1 X1
       have i₂ := eq411 X1 X0
       grind)
    | (have i₁ := eq99 X2 X1 X1
       have i₂ := eq411 X0 X1
       grind)
    | exact superpose eq411 eq99
    | exact resolve eq99 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq3238 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq278 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq278
    | (have j0 := eq278 (τ X0)
       grind)
    | exact resolve eq278 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq3249 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3238 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3238
    | (have j0 := eq3238 X0
       grind)
    | exact resolve eq3238 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3238
  have eq3256 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3249 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3249
    | (have j0 := eq3249 X0
       grind)
    | exact resolve eq3249 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3249
  have eq7046 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq248
       have i₂ := eq519 X0 x y
       grind)
    | exact superpose eq519 eq248
    | (have j1 := eq519 (σ x) x (σ y)
       grind)
    | exact resolve eq248 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq519
  have eq7050 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq7046 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7046
  have eq7191 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq16 X0 (k (τ X0) (τ X0))
       have i₂ := eq285 (τ X0)
       grind)
    | exact superpose eq285 eq16
    | (have j1 := eq285 (τ X0)
       grind)
    | exact resolve eq16 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq285
  have eq7225 : ∀ X0 : G, (σ (τ X0)) = (k X0 (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7191 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq7191
    | (have j0 := eq7191 X0
       grind)
    | exact resolve eq7191 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq7191
  have eq7246 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7225 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7225
    | (have j0 := eq7225 X0
       grind)
    | exact resolve eq7225 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7225
  have eq7255 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7246 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7246
    | (have j0 := eq7246 X0
       grind)
    | exact resolve eq7246 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7246
  have eq8694 : ∀ X0 X1 : G, (k X0 (τ (σ y))) = X0 ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq546 (σ x) X0
       have i₂ := eq7050 X1
       grind)
    | exact superpose eq7050 eq546
    | (have j1 := eq7050 X1
       grind)
    | exact resolve eq546 eq7050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7050
  have eq8888 : ∀ X0 X1 : G, (k X0 y) = X0 ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8694 X0 X1
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq8694
    | (have j0 := eq8694 X0 X1
       grind)
    | exact resolve eq8694 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8694
  have eq9143 : ∀ X0 : G, y = (k y y) ∨ y = (M.op y y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq7255 y
       have i₂ := eq8888 y X0
       grind)
    | exact superpose eq8888 eq7255
    | (have j0 := eq7255 y
       have j1 := eq8888 y y
       grind)
    | exact resolve eq7255 eq8888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7255 eq8888
  have eq9338 : ∀ X0 : G, y = (k y y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq9143 X0
       have j1 := eq73 y y
       grind)
    | (have r₁ := eq9143 X0
       have r₂ := eq73 y y
       grind)
    | (have r₁ := eq9143 y
       have r₂ := eq73 y y
       grind)
    | exact resolve eq9143 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq9143
  have eq9343 : y = (k y y) := by
    first
    | (have j1 := eq534 x y
       grind)
    | (have r₁ := eq9338 x
       have r₂ := eq534 x y
       grind)
    | exact resolve eq9338 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534 eq9338
  have eq9961 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq9343
       grind)
    | exact superpose eq9343 eq12
    | (have j0 := eq12 y y
       grind)
    | exact resolve eq12 eq9343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9343
  have eq9966 : y = (M.op y y) := by grind
  clear eq9961
  have eq10465 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op y X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 y X0
       have i₂ := eq9966
       grind)
    | exact superpose eq9966 eq54
    | exact resolve eq54 eq9966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq10492 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq411 X0 y
       have i₂ := eq9966
       grind)
    | exact superpose eq9966 eq411
    | exact resolve eq411 eq9966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq10497 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq530 y X1 X0
       have i₂ := eq9966
       grind)
    | exact superpose eq9966 eq530
    | exact resolve eq530 eq9966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq10499 : ∀ X0 : G, (k X0 (τ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq546 y X0
       have i₂ := eq9966
       grind)
    | exact superpose eq9966 eq546
    | exact resolve eq546 eq9966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq10502 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq592 X0 X1 y
       have i₂ := eq9966
       grind)
    | exact superpose eq9966 eq592
    | exact resolve eq592 eq9966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq10508 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) y) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq989 y X0 X1
       have i₂ := eq9966
       grind)
    | exact superpose eq9966 eq989
    | exact resolve eq989 eq9966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989 eq9966
  have eq10545 : ∀ X1 : G, (M.op (M.op y X1) y) = X1 := by
    intro X1
    first
    | (have i₁ := eq10465 x X1
       have i₂ := eq10497 x (M.op y X1)
       grind)
    | exact superpose eq10497 eq10465
    | exact resolve eq10465 eq10497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10465
  have eq13545 : (τ y) ≠ (τ y) ∨ (τ y) = (M.op (τ y) (τ y)) := by
    first
    | (have i₁ := eq3256 (τ y)
       have i₂ := eq10499 (τ y)
       grind)
    | exact superpose eq10499 eq3256
    | (have j0 := eq3256 (τ y)
       grind)
    | (have r₁ := eq3256 (τ y)
       have r₂ := eq10499 (τ y)
       grind)
    | exact resolve eq3256 eq10499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3256 eq10499
  have eq13572 : (τ y) = (M.op (τ y) (τ y)) := by grind
  clear eq13545
  have eq13592 : y = (τ y) := by
    first
    | (have i₁ := eq13572
       have i₂ := eq10492 (τ y)
       grind)
    | exact superpose eq10492 eq13572
    | exact resolve eq13572 eq10492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13572
  have eq13621 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 X2)) X3) = (k (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 X2)) X3) ∨ (M.op (M.op X4 X4) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 X2))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq123 X0 (M.op (M.op X2 X2) (M.op X1 X1)) X2
       have i₂ := eq46 (M.op (M.op X2 X2) (M.op X1 X1)) X1 X2 X3
       grind)
    | (have i₁ := eq123 X0 (M.op X3 X3) X2
       have i₂ := eq46 (M.op X3 X3) X1 X2 X3
       grind)
    | exact superpose eq46 eq123
    | exact resolve eq123 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq123
  have eq14165 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) y) X3) = (k (M.op (M.op (M.op X0 X0) (M.op X1 X1)) y) X3) ∨ (M.op (M.op X4 X4) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 X2))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq13621 X0 X1 X1 X3 X4
       have i₂ := eq10502 (M.op (M.op X0 X0) (M.op X1 X1)) X1
       grind)
    | exact superpose eq10502 eq13621
    | (have j0 := eq13621 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq13621 eq10502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13621
  have eq14251 : ∀ X0 X1 X2 X3 X4 : G, (k (M.op X0 X0) X3) = (M.op (M.op X0 X0) X3) ∨ (M.op (M.op X4 X4) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 X2))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14165 X0 X1 X2 X3 X4
       have i₂ := eq10508 (M.op X0 X0) X1
       grind)
    | exact superpose eq10508 eq14165
    | (have j0 := eq14165 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq14165 eq10508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10508 eq14165
  have eq14310 : ∀ X0 X1 X2 X3 X4 : G, (k (M.op X0 X0) X3) = (M.op X3 y) ∨ (M.op (M.op X4 X4) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 X2))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14251 X0 X1 X2 X3 X4
       have i₂ := eq10497 X0 X3
       grind)
    | exact superpose eq10497 eq14251
    | (have j0 := eq14251 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq14251 eq10497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14251
  have eq14359 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 y) = (k y X3) ∨ (M.op (M.op X4 X4) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 X2))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14310 X0 X1 X2 X3 X4
       have i₂ := eq10492 X0
       grind)
    | exact superpose eq10492 eq14310
    | (have j0 := eq14310 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq14310 eq10492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14310
  have eq14392 : ∀ X2 X3 : G, (M.op X2 X2) = X3 ∨ (M.op X3 y) = (k y X3) := by
    intro X2 X3
    first
    | (have i₁ := eq14359 x x X2 X3 x
       have i₂ := eq846 x x x (M.op X2 X2)
       grind)
    | exact superpose eq846 eq14359
    | (have j0 := eq14359 x x X2 X3 x
       grind)
    | exact resolve eq14359 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846 eq14359
  have eq14415 : ∀ X3 : G, (M.op X3 y) = (k y X3) ∨ y = X3 := by
    intro X3
    first
    | (have i₁ := eq14392 x X3
       have i₂ := eq10492 x
       grind)
    | exact superpose eq10492 eq14392
    | (have j0 := eq14392 x X3
       grind)
    | exact resolve eq14392 eq10492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14392
  have eq14443 : y = (σ y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq13592
       grind)
    | exact superpose eq13592 eq10
    | exact resolve eq10 eq13592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16415 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq14443
       grind)
    | exact superpose eq14443 eq14
    | exact resolve eq14 eq14443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20646 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op (M.op X1 X1) y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq886 y X1 (M.op y X0)
       have i₂ := eq10545 X0
       grind)
    | exact superpose eq10545 eq886
    | exact resolve eq886 eq10545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq20647 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y y) X0) := by
    intro X0
    first
    | (have i₁ := eq20646 X0 x
       have i₂ := eq10497 x y
       grind)
    | exact superpose eq10497 eq20646
    | exact resolve eq20646 eq10497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20646
  have eq20681 : ∀ X0 : G, (M.op y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq20647 X0
       have i₂ := eq10497 y X0
       grind)
    | exact superpose eq10497 eq20647
    | exact resolve eq20647 eq10497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10497 eq20647
  have eq23180 : ∀ X0 : G, (M.op y (M.op y X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq10545 X0
       have i₂ := eq20681 (M.op y X0)
       grind)
    | exact superpose eq20681 eq10545
    | exact resolve eq10545 eq20681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10545
  have eq33038 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (σ X1) (M.op (M.op X2 X2) (M.op X3 X3))) = (M.op (M.op (σ (k X0 X1)) (M.op (M.op X4 X4) (M.op X5 X5))) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq110 (σ X0) (σ X1) X4 X5 X2 X3
       have i₂ := eq259 X0 X1
       grind)
    | exact superpose eq259 eq110
    | (have j1 := eq259 X0 X1
       grind)
    | exact resolve eq110 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq259
  have eq34141 : ∀ X0 X1 X2 X3 X4 : G, (M.op (σ X1) (M.op (M.op X2 X2) (M.op X3 X3))) = (M.op (M.op (σ (k X0 X1)) (M.op (M.op X4 X4) y)) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq33038 X0 X1 X2 X3 X4 x
       have i₂ := eq10502 (M.op X4 X4) x
       grind)
    | exact superpose eq10502 eq33038
    | (have j0 := eq33038 X0 X1 X2 X3 X4 x
       grind)
    | exact resolve eq33038 eq10502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33038
  have eq34664 : ∀ X0 X1 X2 X3 X4 : G, (M.op (σ X1) (M.op (M.op X2 X2) (M.op X3 X3))) = (M.op (M.op (σ (k X0 X1)) (M.op y (M.op X4 X4))) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq34141 X0 X1 X2 X3 X4
       have i₂ := eq20681 (M.op X4 X4)
       grind)
    | exact superpose eq20681 eq34141
    | (have j0 := eq34141 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq34141 eq20681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34141
  have eq35150 : ∀ X0 X1 X2 X3 : G, (M.op (σ X1) (M.op (M.op X2 X2) (M.op X3 X3))) = (M.op (M.op (σ (k X0 X1)) (M.op y y)) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq34664 X0 X1 X2 X3 x
       have i₂ := eq10502 y x
       grind)
    | exact superpose eq10502 eq34664
    | (have j0 := eq34664 X0 X1 X2 X3 x
       grind)
    | exact resolve eq34664 eq10502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34664
  have eq35607 : ∀ X0 X1 X2 X3 : G, (M.op (σ X1) (M.op (M.op X2 X2) (M.op X3 X3))) = (M.op (M.op (σ (k X0 X1)) y) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq35150 X0 X1 X2 X3
       have i₂ := eq10502 (σ (k X0 X1)) y
       grind)
    | exact superpose eq10502 eq35150
    | (have j0 := eq35150 X0 X1 X2 X3
       grind)
    | exact resolve eq35150 eq10502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35150
  have eq35993 : ∀ X0 X1 X2 X3 : G, (M.op (σ X1) (M.op (M.op X2 X2) (M.op X3 X3))) = (M.op (M.op y (σ (k X0 X1))) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq35607 X0 X1 X2 X3
       have i₂ := eq20681 (σ (k X0 X1))
       grind)
    | exact superpose eq20681 eq35607
    | (have j0 := eq35607 X0 X1 X2 X3
       grind)
    | exact resolve eq35607 eq20681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35607
  have eq36319 : ∀ X0 X1 X2 : G, (M.op (σ X1) (M.op (M.op X2 X2) y)) = (M.op (M.op y (σ (k X0 X1))) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35993 X0 X1 X2 x
       have i₂ := eq10502 (M.op X2 X2) x
       grind)
    | exact superpose eq10502 eq35993
    | (have j0 := eq35993 X0 X1 X2 x
       grind)
    | exact resolve eq35993 eq10502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35993
  have eq36588 : ∀ X0 X1 X2 : G, (M.op (σ X1) (M.op y (M.op X2 X2))) = (M.op (M.op y (σ (k X0 X1))) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36319 X0 X1 X2
       have i₂ := eq20681 (M.op X2 X2)
       grind)
    | exact superpose eq20681 eq36319
    | (have j0 := eq36319 X0 X1 X2
       grind)
    | exact resolve eq36319 eq20681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36319
  have eq36826 : ∀ X0 X1 : G, (M.op (σ X1) (M.op y y)) = (M.op (M.op y (σ (k X0 X1))) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq36588 X0 X1 x
       have i₂ := eq10502 y x
       grind)
    | exact superpose eq10502 eq36588
    | (have j0 := eq36588 X0 X1 x
       grind)
    | exact resolve eq36588 eq10502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36588
  have eq36976 : ∀ X0 X1 : G, (M.op (σ X1) y) = (M.op (M.op y (σ (k X0 X1))) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq36826 X0 X1
       have i₂ := eq10502 (σ X1) y
       grind)
    | exact superpose eq10502 eq36826
    | (have j0 := eq36826 X0 X1
       grind)
    | exact resolve eq36826 eq10502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10502 eq36826
  have eq37078 : ∀ X0 X1 : G, (M.op y (σ X1)) = (M.op (M.op y (σ (k X0 X1))) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq36976 X0 X1
       have i₂ := eq20681 (σ X1)
       grind)
    | exact superpose eq20681 eq36976
    | (have j0 := eq36976 X0 X1
       grind)
    | exact resolve eq36976 eq20681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36976
  have eq37145 : ∀ X0 X1 : G, (τ y) = X1 ∨ (M.op y (σ X1)) = (M.op (M.op y (σ (k X0 X1))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq37078 X0 X1
       have i₂ := eq10492 (σ X0)
       grind)
    | exact superpose eq10492 eq37078
    | (have j0 := eq37078 X0 X1
       grind)
    | exact resolve eq37078 eq10492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37078
  have eq37170 : ∀ X0 X1 : G, (M.op y (σ X1)) = (M.op (M.op y (σ (k X0 X1))) (σ X0)) ∨ y = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37145 X0 X1
       have i₂ := eq13592
       grind)
    | exact superpose eq13592 eq37145
    | (have j0 := eq37145 X0 X1
       grind)
    | exact resolve eq37145 eq13592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13592 eq37145
  have eq286838 : ∀ X0 : G, (M.op y (σ X0)) = (M.op (M.op y (σ (M.op X0 y))) (σ y)) ∨ y = X0 ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq37170 y X0
       have i₂ := eq14415 X0
       grind)
    | exact superpose eq14415 eq37170
    | (have j0 := eq37170 X0 X0
       have j1 := eq14415 X0
       grind)
    | exact resolve eq37170 eq14415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14415 eq37170
  have eq286881 : ∀ X0 : G, (M.op y (σ X0)) = (M.op (M.op y (σ (M.op X0 y))) (σ y)) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq286838 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286838
  have eq286920 : ∀ X0 : G, (M.op y (σ X0)) = (M.op (M.op y (σ (M.op X0 y))) y) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq286881 X0
       have i₂ := eq14443
       grind)
    | exact superpose eq14443 eq286881
    | (have j0 := eq286881 X0
       grind)
    | exact resolve eq286881 eq14443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286881
  have eq286962 : ∀ X0 : G, (M.op y (σ X0)) = (M.op y (M.op y (σ (M.op X0 y)))) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq286920 X0
       have i₂ := eq20681 (M.op y (σ (M.op X0 y)))
       grind)
    | exact superpose eq20681 eq286920
    | (have j0 := eq286920 X0
       grind)
    | exact resolve eq286920 eq20681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286920
  have eq286996 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op y (σ X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq286962 X0
       have i₂ := eq23180 (σ (M.op X0 y))
       grind)
    | exact superpose eq23180 eq286962
    | (have j0 := eq286962 X0
       grind)
    | exact resolve eq286962 eq23180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23180 eq286962
  have eq287064 : (M.op (σ x) y) ≠ (M.op y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq16415
       have i₂ := eq286996 x
       grind)
    | exact superpose eq286996 eq16415
    | (have j1 := eq286996 x
       grind)
    | exact resolve eq16415 eq286996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16415 eq286996
  have eq287093 : x = y := by
    first
    | (have r₁ := eq287064
       have r₂ := eq20681 (σ x)
       grind)
    | exact resolve eq287064 eq20681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20681 eq287064
  have eq287153 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq287093
       grind)
    | exact superpose eq287093 eq14
    | exact resolve eq14 eq287093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287093
  have eq287387 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq287153
       have i₂ := eq10492 x
       grind)
    | exact superpose eq10492 eq287153
    | exact resolve eq287153 eq10492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287153
  have eq287432 : y ≠ (σ y) := by
    first
    | (have i₁ := eq287387
       have i₂ := eq10492 (σ x)
       grind)
    | exact superpose eq10492 eq287387
    | exact resolve eq287387 eq10492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10492 eq287387
  have eq287459 : False := by grind
  exact eq287459

/-- `Equation703`: `x = y ◇ (y ◇ ((x ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_x_pyx_pxy_Equation703 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law703 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law703.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op (M.op X0 X0) X0))) = X0 := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq21 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq8 (M.op (M.op X0 X0) X0) (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       have i₂ := eq8 X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq30 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 (M.op X1 (M.op (M.op X0 X0) X0))) = (M.op (M.op X1 (M.op (M.op X0 X0) X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X1 (M.op (M.op X0 X0) X0))
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 X1 (M.op X1 (M.op (M.op X0 X0) X0))
       grind)
    | (have r₁ := eq11 X0 (M.op X0 (M.op (M.op X0 X0) X0))
       have r₂ := eq8 X0 X0
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  clear eq20
  have eq40 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq41 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) := by
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
  have eq63 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq40 x y
       grind)
    | exact superpose eq40 eq14
    | (have j1 := eq40 x y
       grind)
    | exact resolve eq14 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq84 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0)) (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0))) (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 (M.op (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0)) (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0)))
       have i₂ := eq21 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 : G, (k X0 (M.op X0 (M.op (M.op X0 X0) X0))) = (M.op (M.op X0 (M.op (M.op X0 X0) X0)) X0) := by
    intro X0
    first
    | (have j0 := eq30 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq234 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ (M.op (τ X1) (M.op (M.op X0 X0) X0)))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 (M.op (τ X0) (M.op (M.op X0 X0) X0))
       have i₂ := eq8 X0 (τ X0)
       grind)
    | exact superpose eq8 eq41
    | exact resolve eq41 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq275 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq63
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq63
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq63 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq276 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq275
  have eq871 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq21 (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0))
       have i₂ := eq84 X0
       grind)
    | exact superpose eq84 eq21
    | exact resolve eq21 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq872 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq84 X0
       grind)
    | exact superpose eq84 eq8
    | exact resolve eq8 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1140 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (τ (σ (M.op (τ (σ X1)) (M.op (M.op X0 X0) X0))))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27 X1 (σ (M.op (τ (σ X1)) (M.op (M.op X0 X0) X0)))
       have i₂ := eq234 X0 (σ X1)
       grind)
    | exact superpose eq234 eq27
    | (have j1 := eq234 (k X1 (τ (σ (M.op (τ (σ X1)) (M.op (M.op X0 X0) X0))))) (σ X0)
       grind)
    | exact resolve eq27 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq234
  have eq1162 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (M.op (τ (σ X1)) (M.op (M.op X0 X0) X0))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1140 X0 X1
       have i₂ := eq9 (M.op (τ (σ X1)) (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq9 eq1140
    | (have j0 := eq1140 (k X1 (M.op (τ (σ X1)) (M.op (M.op X0 X0) X0))) X0
       grind)
    | exact resolve eq1140 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq1188 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (M.op X1 (M.op (M.op X0 X0) X0))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1162 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq1162
    | (have j0 := eq1162 (k X1 (M.op X1 (M.op (M.op X0 X0) X0))) X0
       grind)
    | exact resolve eq1162 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162
  have eq1199 : ∀ X0 X1 : G, (k X1 (M.op X1 (M.op (M.op X0 X0) X0))) = X0 ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1188 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1188
    | (have j0 := eq1188 X0 X1
       grind)
    | exact resolve eq1188 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq1206 : ∀ X0 X1 : G, (k X1 (M.op X1 (M.op (M.op X0 X0) X0))) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1199 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq1199
    | (have j0 := eq1199 X0 X1
       grind)
    | exact resolve eq1199 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199
  have eq7892 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq872 X1 X2
       have i₂ := eq872 X1 X0
       grind)
    | exact superpose eq872 eq872
    | exact resolve eq872 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7901 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq871 X1
       have i₂ := eq872 X1 X0
       grind)
    | exact superpose eq872 eq871
    | exact resolve eq871 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq7902 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0
       have i₂ := eq872 X0 X1
       grind)
    | exact superpose eq872 eq84
    | exact resolve eq84 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq7904 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (M.op X1 X1) X1) X2
       have i₂ := eq872 X1 X0
       grind)
    | exact superpose eq872 eq8
    | exact resolve eq8 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq7959 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op (M.op X0 X0) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7892 X1 (M.op X2 (M.op (M.op X0 X0) X0)) X2
       have i₂ := eq8 X0 X2
       grind)
    | exact superpose eq8 eq7892
    | exact resolve eq7892 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7963 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X3 X1))) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7892 X2 (M.op X3 X1) X3
       have i₂ := eq7892 X3 X1 X0
       grind)
    | (have i₁ := eq7892 X2 (M.op X3 X1) X3
       have i₂ := eq7892 X0 X1 X3
       grind)
    | exact superpose eq7892 eq7892
    | exact resolve eq7892 eq7892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7971 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op X0 (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7892 X0 (σ y) (σ x)
       have i₂ := eq276
       grind)
    | exact superpose eq276 eq7892
    | exact resolve eq7892 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq8225 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2)))) = (M.op X3 (M.op X3 (M.op X4 (M.op X4 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7904 X4 X2 X3
       have i₂ := eq7904 X1 X2 X0
       grind)
    | exact superpose eq7904 eq7904
    | exact resolve eq7904 eq7904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8257 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7904 X1 X2 X1
       have i₂ := eq7892 X1 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq7904 X1 X2 X1
       have i₂ := eq7892 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq7892 eq7904
    | exact resolve eq7904 eq7892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8260 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X3) = (M.op (M.op (M.op X2 (M.op X2 X3)) (M.op X2 (M.op X2 X3))) (M.op X0 (M.op X0 (M.op X1 (M.op X1 (M.op X2 (M.op X2 X3))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7904 X2 X3 (M.op (M.op X2 (M.op X2 X3)) (M.op X2 (M.op X2 X3)))
       have i₂ := eq7904 X1 (M.op X2 (M.op X2 X3)) X0
       grind)
    | exact superpose eq7904 eq7904
    | exact resolve eq7904 eq7904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8264 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2)))))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3
       have i₂ := eq7904 X1 X2 X0
       grind)
    | exact superpose eq7904 eq8
    | exact resolve eq8 eq7904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8331 : ∀ X2 X3 : G, (M.op (M.op X3 X3) X3) = (M.op (M.op (M.op X2 (M.op X2 X3)) (M.op X2 (M.op X2 X3))) X3) := by
    intro X2 X3
    first
    | (have i₁ := eq8260 x x X2 X3
       have i₂ := eq8264 x X2 X3 x
       grind)
    | exact superpose eq8264 eq8260
    | exact resolve eq8260 eq8264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8260 eq8264
  have eq8698 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X1 (M.op (M.op X0 X0) X0))) = (M.op X2 (M.op X4 (M.op X4 (M.op X2 (M.op X3 (M.op X3 X0)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7963 X4 (M.op X2 (M.op X3 (M.op X3 X0))) X1 X2
       have i₂ := eq7904 X3 X0 X2
       grind)
    | exact superpose eq7904 eq7963
    | exact resolve eq7963 eq7904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8739 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op X0 (M.op X4 (M.op X4 X2))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq7963 X4 X2 x X0
       have i₂ := eq7963 X1 X2 x X0
       grind)
    | (have i₁ := eq7963 X0 X1 X0 X0
       have i₂ := eq7963 X0 X1 X2 X0
       grind)
    | exact superpose eq7963 eq7963
    | exact resolve eq7963 eq7963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8860 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 (M.op X3 X2)) (M.op X3 (M.op X3 X2))) (M.op X3 (M.op X3 X2))) = (M.op X4 (M.op X4 (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7904 X1 (M.op X3 (M.op X3 X2)) X4
       have i₂ := eq7963 X3 X2 X0 X1
       grind)
    | (have i₁ := eq7904 X2 (M.op X2 (M.op X3 X1)) X2
       have i₂ := eq7963 X0 X1 X2 X3
       grind)
    | exact superpose eq7963 eq7904
    | exact resolve eq7904 eq7963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8873 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (k X3 (M.op X3 (M.op X0 (M.op X0 (M.op (M.op (M.op X1 (M.op X1 X2)) (M.op X1 (M.op X1 X2))) X2))))) ∨ (M.op X1 (M.op X1 X2)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1206 (M.op X1 (M.op X1 X2)) X3
       have i₂ := eq7963 X1 X2 X0 (M.op (M.op X1 (M.op X1 X2)) (M.op X1 (M.op X1 X2)))
       grind)
    | exact superpose eq7963 eq1206
    | (have j0 := eq1206 (M.op X1 (M.op X1 X2)) (k X3 (M.op X3 (M.op X0 (M.op X0 (M.op (M.op (M.op X1 (M.op X1 X2)) (M.op X1 (M.op X1 X2))) X2)))))
       grind)
    | exact resolve eq1206 eq7963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206
  have eq8889 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (k X3 (M.op X3 (M.op X0 (M.op X0 (M.op (M.op X2 X2) X2))))) ∨ (M.op X1 (M.op X1 X2)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8873 X0 X1 X2 X3
       have i₂ := eq8331 X1 X2
       grind)
    | exact superpose eq8331 eq8873
    | (have j0 := eq8873 X0 X1 X2 (k X3 (M.op X3 (M.op X0 (M.op X0 (M.op (M.op X2 X2) X2)))))
       grind)
    | exact resolve eq8873 eq8331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8331 eq8873
  have eq8901 : ∀ X0 X1 X2 X4 : G, (M.op X4 (M.op X4 (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))))) = X2 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq8860 X0 X1 X2 x X4
       have i₂ := eq7902 x X2
       grind)
    | exact superpose eq7902 eq8860
    | exact resolve eq8860 eq7902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7902 eq8860
  have eq8930 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op X4 (M.op X4 (M.op X2 (M.op X3 (M.op X3 X0)))))) = X0 := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq8698 X0 x X2 X3 X4
       have i₂ := eq8 X0 x
       grind)
    | exact superpose eq8 eq8698
    | exact resolve eq8698 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8698
  have eq8934 : ∀ X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (k X3 (M.op X3 X2)) ∨ (M.op X1 (M.op X1 X2)) = X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq8889 x X1 X2 X3
       have i₂ := eq8 X2 x
       grind)
    | exact superpose eq8 eq8889
    | (have j0 := eq8889 x X1 X2 (k X3 (M.op X3 X2))
       grind)
    | exact resolve eq8889 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8889
  have eq9237 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X0) X0)) = (M.op X1 (M.op X1 (M.op X2 (M.op X2 (M.op X3 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7892 X1 (M.op X2 (M.op X2 (M.op X3 X0))) X3
       have i₂ := eq8257 X2 X3 X0
       grind)
    | exact superpose eq8257 eq7892
    | exact resolve eq7892 eq8257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10093 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op X2 (M.op X2 X1))) (M.op X0 (M.op X0 X1))) = (M.op X3 (M.op X4 (M.op X4 (M.op X3 (M.op X0 (M.op X0 X1)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8257 X4 X3 (M.op X0 (M.op X0 X1))
       have i₂ := eq8739 (M.op X0 (M.op X0 X1)) X0 X1 X2
       grind)
    | (have i₁ := eq8257 X4 X3 (M.op X0 (M.op X0 X1))
       have i₂ := eq8739 (M.op X0 (M.op X0 X1)) X2 X1 X0
       grind)
    | exact superpose eq8739 eq8257
    | exact resolve eq8257 eq8739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8739
  have eq10142 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op X2 (M.op X2 X1))) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10093 X0 X1 X2 x x
       have i₂ := eq8930 X1 x X0 x
       grind)
    | exact superpose eq8930 eq10093
    | exact resolve eq10093 eq8930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8930 eq10093
  have eq10513 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X1 (M.op X1 (M.op X0 (M.op X2 X3)))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8901 X0 X2 X3 X2
       have i₂ := eq7963 X1 (M.op X0 (M.op X2 X3)) X2 X0
       grind)
    | (have i₁ := eq8901 X0 X0 X2 X3
       have i₂ := eq7963 X0 (M.op X0 (M.op X0 X2)) X2 X3
       grind)
    | exact superpose eq7963 eq8901
    | exact resolve eq8901 eq7963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7963 eq8901
  have eq15434 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X1)) = (k X0 (M.op X0 X1)) ∨ (M.op X3 (M.op X3 X1)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7892 X2 X1 X3
       have i₂ := eq8934 X3 X1 X0
       grind)
    | exact superpose eq8934 eq7892
    | (have j1 := eq8934 X2 X1 X0
       grind)
    | exact resolve eq7892 eq8934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8934
  have eq18008 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X0) = X1 ∨ (M.op X2 (M.op X2 X1)) = (k X0 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 (M.op X1 X1)
       have i₂ := eq15434 X0 X1 X2 (M.op X1 X1)
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq15434 (M.op X1 (M.op (M.op X0 X0) X0)) X1 X2 x
       grind)
    | exact superpose eq15434 eq8
    | (have j1 := eq15434 X0 X1 X2 x
       grind)
    | exact resolve eq8 eq15434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20847 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) X1) = (M.op (M.op X0 X0) (M.op X2 (M.op X2 X0))) ∨ (k X1 (M.op X1 X0)) = (M.op X3 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8257 X2 (M.op X0 X0) X1
       have i₂ := eq18008 X1 X0 X3
       grind)
    | exact superpose eq18008 eq8257
    | (have j1 := eq18008 X1 X0 X3
       grind)
    | exact resolve eq8257 eq18008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8257 eq18008
  have eq21193 : ∀ X0 X1 X3 : G, (M.op (M.op X1 X1) X1) = X0 ∨ (k X1 (M.op X1 X0)) = (M.op X3 (M.op X3 X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq20847 X0 X1 x X3
       have i₂ := eq7901 x X0
       grind)
    | exact superpose eq7901 eq20847
    | (have j0 := eq20847 X0 X1 x X3
       grind)
    | exact resolve eq20847 eq7901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20847
  have eq22698 : ∀ X0 X1 X2 : G, (k X1 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op (M.op X0 X0) X0)))) ∨ (M.op X1 (M.op (M.op X0 X0) X0)) = (M.op (M.op X1 X1) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21193 (M.op X1 (M.op (M.op X0 X0) X0)) X1 X2
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq21193
    | (have j0 := eq21193 (M.op X1 (M.op (M.op X0 X0) X0)) X1 x
       grind)
    | exact resolve eq21193 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21193
  have eq23267 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X0)) = (M.op (M.op X1 X1) X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22698 X0 X1 x
       have i₂ := eq7959 X0 x X1
       grind)
    | exact superpose eq7959 eq22698
    | (have j0 := eq22698 X0 X1 x
       grind)
    | exact resolve eq22698 eq7959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7959 eq22698
  have eq27357 : ∀ X0 X1 X2 X3 X4 X6 : G, (M.op X1 (M.op X1 (M.op X2 (M.op X2 X3)))) = (M.op X4 (M.op X4 X0)) ∨ (k X0 (M.op X0 X3)) = (M.op X6 (M.op X6 X3)) := by
    intro X0 X1 X2 X3 X4 X6
    first
    | (have i₁ := eq8225 X1 X2 X3 X4 x
       have i₂ := eq15434 X0 X3 X6 x
       grind)
    | (have i₁ := eq8225 X0 X1 X2 X3 X4
       have i₂ := eq15434 (M.op X4 (M.op X4 X2)) X1 X2 X3
       grind)
    | exact superpose eq15434 eq8225
    | (have j1 := eq15434 X0 X3 X6 X3
       grind)
    | exact resolve eq8225 eq15434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8225 eq15434
  have eq89230 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0
       have i₂ := eq23267 X1 X0
       grind)
    | exact superpose eq23267 eq8
    | (have j1 := eq23267 X1 X0
       grind)
    | exact resolve eq8 eq23267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23267
  have eq89438 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0
       have i₂ := eq89230 X0 X1
       grind)
    | (have i₁ := eq101 X0
       have i₂ := eq89230 X0 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq89230 eq101
    | (have j1 := eq89230 X1 X0
       grind)
    | exact resolve eq101 eq89230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq89230
  have eq89711 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq89438 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89438
  have eq89750 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2)))) ≠ (M.op X2 (M.op X2 X2)) ∨ (M.op X2 (M.op X2 X2)) = (k X2 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq89711 X2 (M.op X2 X2)
       have i₂ := eq7904 X1 X2 X0
       grind)
    | exact superpose eq7904 eq89711
    | (have j0 := eq89711 X2 (M.op X2 X2)
       grind)
    | exact resolve eq89711 eq7904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7904
  have eq89754 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq89711 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89711
  have eq89757 : ∀ X2 : G, (M.op X2 (M.op X2 X2)) = (k X2 (M.op X2 X2)) := by
    intro X2
    first
    | (have j0 := eq89750 x x X2
       have j1 := eq27357 X2 x X2 X2 x X2
       grind)
    | (have r₁ := eq89750 x X2 x
       have r₂ := eq27357 x x X2 x x x
       grind)
    | (have r₁ := eq89750 x x (M.op X2 (M.op X2 x))
       have r₂ := eq27357 (M.op x (M.op x (M.op X2 (M.op X2 x)))) (M.op X2 (M.op X2 x)) X2 x x x
       grind)
    | exact resolve eq89750 eq27357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27357 eq89750
  have eq89911 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq89754 (σ X0)
       grind)
    | exact superpose eq89754 eq13
    | exact resolve eq13 eq89754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89940 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq89754 (τ X0)
       grind)
    | exact superpose eq89754 eq31
    | exact resolve eq31 eq89754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90028 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq89940 X0
       have i₂ := eq89754 X0
       grind)
    | exact superpose eq89754 eq89940
    | exact resolve eq89940 eq89754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89940
  have eq90056 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq89911 X0
       have i₂ := eq89754 X0
       grind)
    | exact superpose eq89754 eq89911
    | exact resolve eq89911 eq89754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89754 eq89911
  have eq90534 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (τ X0))) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7892 X1 (τ X0) (τ X0)
       have i₂ := eq90028 X0
       grind)
    | exact superpose eq90028 eq7892
    | exact resolve eq7892 eq90028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91034 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0))) = (M.op X1 (M.op X1 (M.op X2 (M.op X2 (σ (M.op X0 X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9237 (σ X0) X1 X2 (σ X0)
       have i₂ := eq90056 X0
       grind)
    | exact superpose eq90056 eq9237
    | exact resolve eq9237 eq90056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91266 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (k (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq89757 (τ X0)
       have i₂ := eq90028 X0
       grind)
    | exact superpose eq90028 eq89757
    | exact resolve eq89757 eq90028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90028
  have eq91357 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq91266 X0
       have i₂ := eq31 (M.op X0 X0) X0
       grind)
    | exact superpose eq31 eq91266
    | exact resolve eq91266 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq91266
  have eq91388 : ∀ X0 : G, (τ (M.op X0 (M.op X0 X0))) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq91357 X0
       have i₂ := eq89757 X0
       grind)
    | exact superpose eq89757 eq91357
    | exact resolve eq91357 eq89757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89757 eq91357
  have eq93974 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (τ X0))) = (τ (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq90534 X0 X1
       have i₂ := eq91388 X0
       grind)
    | exact superpose eq91388 eq90534
    | exact resolve eq90534 eq91388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90534 eq91388
  have eq94110 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (τ X1))) = (τ (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq93974 X1 X2
       have i₂ := eq7892 X1 X1 X0
       grind)
    | (have i₁ := eq93974 X1 X2
       have i₂ := eq7892 X0 X1 X1
       grind)
    | exact superpose eq7892 eq93974
    | exact resolve eq93974 eq7892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7892
  have eq94143 : ∀ X0 : G, (τ (M.op (σ x) (σ x))) = (M.op X0 (M.op X0 (τ (σ y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq93974 (σ y) X0
       have i₂ := eq7971 (σ y)
       grind)
    | exact superpose eq7971 eq93974
    | exact resolve eq93974 eq7971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7971 eq93974
  have eq94483 : ∀ X0 : G, (τ (M.op (σ x) (σ x))) = (M.op X0 (M.op X0 y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq94143 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq94143
    | exact resolve eq94143 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94143
  have eq94563 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (τ (σ (M.op x x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq94483 X0
       have i₂ := eq90056 x
       grind)
    | exact superpose eq90056 eq94483
    | exact resolve eq94483 eq90056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94483
  have eq94599 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op X0 y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq94563 X0
       have i₂ := eq9 (M.op x x)
       grind)
    | exact superpose eq9 eq94563
    | exact resolve eq94563 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94563
  have eq94642 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = (τ (M.op X2 (M.op X2 (σ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq94110 X2 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq94110
    | exact resolve eq94110 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94110
  have eq96822 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 (σ (M.op (M.op X1 X1) X1))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7901 (M.op X1 X1) X1
       have i₂ := eq94642 (M.op (M.op X1 X1) X1) (M.op X1 X1) X0
       grind)
    | exact superpose eq94642 eq7901
    | exact resolve eq7901 eq94642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7901
  have eq96844 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X0 X1))) = (M.op X2 (M.op X2 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X2 (M.op X2 (σ X1)))
       have i₂ := eq94642 X1 X0 X2
       grind)
    | exact superpose eq94642 eq10
    | exact resolve eq10 eq94642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94642
  have eq99469 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op (M.op X0 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 (M.op X1 (σ (M.op (M.op X0 X0) X0))))
       have i₂ := eq96822 X1 X0
       grind)
    | exact superpose eq96822 eq10
    | exact resolve eq10 eq96822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96822
  have eq100371 : ∀ X0 X2 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (M.op (σ X0) (M.op X2 (M.op X2 (σ (M.op (M.op X0 X0) X0))))) (σ X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq10142 x (σ (M.op (M.op X0 X0) X0)) X2
       have i₂ := eq99469 X0 x
       grind)
    | exact superpose eq99469 eq10142
    | exact resolve eq10142 eq99469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10142
  have eq100483 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq100371 X0 x
       have i₂ := eq99469 X0 x
       grind)
    | exact superpose eq99469 eq100371
    | exact resolve eq100371 eq99469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100371
  have eq100511 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq100483 X0
       have i₂ := eq90056 X0
       grind)
    | exact superpose eq90056 eq100483
    | exact resolve eq100483 eq90056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90056 eq100483
  have eq102022 : ∀ X0 X1 : G, y = (M.op X0 (M.op X0 (M.op X1 (M.op X1 (M.op x x))))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq10513 X0 X1 X0 y
       have i₂ := eq94599 X0
       grind)
    | exact superpose eq94599 eq10513
    | exact resolve eq10513 eq94599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94599
  have eq102119 : y = (M.op x (M.op (M.op x x) x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq102022 x x
       have i₂ := eq9237 x x x x
       grind)
    | exact superpose eq9237 eq102022
    | exact resolve eq102022 eq9237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9237 eq102022
  have eq103345 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8 x x
       have i₂ := eq102119
       grind)
    | exact superpose eq102119 eq8
    | exact resolve eq8 eq102119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102119
  have eq103416 : x = (M.op x y) := by grind
  clear eq103345
  have eq103575 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq96844 x y X0
       have i₂ := eq103416
       grind)
    | exact superpose eq103416 eq96844
    | exact resolve eq96844 eq103416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96844
  have eq105683 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op X0 (M.op X1 (M.op X1 (σ (M.op x x)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq10513 X0 X1 X0 (σ y)
       have i₂ := eq103575 X0
       grind)
    | exact superpose eq103575 eq10513
    | exact resolve eq10513 eq103575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10513 eq103575
  have eq105854 : (σ y) = (M.op (σ x) (M.op (σ (M.op x x)) (σ x))) := by
    first
    | (have i₁ := eq105683 x x
       have i₂ := eq91034 x x x
       grind)
    | exact superpose eq91034 eq105683
    | exact resolve eq105683 eq91034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91034 eq105683
  have eq106001 : (σ y) = (M.op (σ x) (σ (M.op (M.op x x) x))) := by
    first
    | (have i₁ := eq105854
       have i₂ := eq100511 x
       grind)
    | exact superpose eq100511 eq105854
    | exact resolve eq105854 eq100511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100511 eq105854
  have eq107502 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq99469 x (σ x)
       have i₂ := eq106001
       grind)
    | exact superpose eq106001 eq99469
    | exact resolve eq99469 eq106001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99469 eq106001
  have eq107659 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq107502
       grind)
    | exact superpose eq107502 eq14
    | exact resolve eq14 eq107502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107502
  have eq107899 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq107659
       have i₂ := eq103416
       grind)
    | exact superpose eq103416 eq107659
    | exact resolve eq107659 eq103416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103416 eq107659
  have eq107900 : False := by grind
  exact eq107900

/-- `Equation72`: `x = y ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_x_pxx_pxy_Equation72 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law72 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law72.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq8 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq8 X0 (M.op X0 X0)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq15 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq8
    | exact resolve eq8 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op X0 X0) X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq11
    | (have j0 := eq11 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq11 (M.op X0 X0) X0
       have r₂ := eq15 X0
       grind)
    | exact resolve eq11 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq24 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq67 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
  have eq270 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq18 X0
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq18
    | exact resolve eq18 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 : G, (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq25 (M.op X0 X0)
       have i₂ := eq18 X0
       grind)
    | exact superpose eq18 eq25
    | exact resolve eq25 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op (M.op X0 X0) (M.op X0 X0)) X1
       have i₂ := eq18 X0
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq15 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq18 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ X0 ∨ (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq18 X0
       grind)
    | exact superpose eq18 eq11
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq281 : ∀ X0 : G, (k (M.op X0 X0) X0) ≠ X0 ∨ (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq280 X0
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq280
    | (have j0 := eq280 X0
       grind)
    | exact resolve eq280 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq286 : ∀ X0 : G, (M.op X0 (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq275 X0
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq275
    | exact resolve eq275 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq288 : ∀ X0 : G, (k (k (M.op X0 X0) X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq272 X0
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq272
    | exact resolve eq272 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq292 : ∀ X0 : G, (k (M.op X0 X0) X0) ≠ X0 ∨ (k (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq281 X0
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq281
    | (have j0 := eq281 X0
       grind)
    | exact resolve eq281 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq363 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq67
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq67
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq67 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq364 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq363
  have eq811 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (k (M.op X0 X0) X0) X1
       have i₂ := eq270 X0
       grind)
    | exact superpose eq270 eq8
    | exact resolve eq8 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq844 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq274 X1 X2
       have i₂ := eq274 X1 X0
       grind)
    | exact superpose eq274 eq274
    | exact resolve eq274 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq862 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X1 X1) X2
       have i₂ := eq274 X1 X0
       grind)
    | exact superpose eq274 eq8
    | exact resolve eq8 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq942 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq286 X1
       have i₂ := eq811 X1 X0
       grind)
    | exact superpose eq811 eq286
    | exact resolve eq286 eq811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286 eq811
  have eq2091 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq862 (σ x) (σ y) X0
       have i₂ := eq364
       grind)
    | exact superpose eq364 eq862
    | exact resolve eq862 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq2109 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq862 X1 X2 X1
       have i₂ := eq844 X1 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq862 X1 X2 X1
       have i₂ := eq844 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq844 eq862
    | exact resolve eq862 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844 eq862
  have eq2257 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2091 x
       have i₂ := eq8 (σ x) x
       grind)
    | exact superpose eq8 eq2091
    | exact resolve eq2091 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2091
  have eq3616 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35 y y
       have i₂ := eq2257
       grind)
    | exact superpose eq2257 eq35
    | exact resolve eq35 eq2257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq3648 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ y)
       have i₂ := eq2257
       grind)
    | exact superpose eq2257 eq11
    | (have r₁ := eq11 x y
       have r₂ := eq2257
       grind)
    | exact resolve eq11 eq2257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2257
  have eq3664 : (σ x) = (σ (k y y)) ∨ (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3648
       have i₂ := eq13 y y
       grind)
    | exact superpose eq13 eq3648
    | exact resolve eq3648 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3648
  have eq3683 : (σ x) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3664
       have r₂ := eq3616
       grind)
    | exact resolve eq3664 eq3616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3616 eq3664
  have eq3814 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq3683
       grind)
    | exact superpose eq3683 eq9
    | exact resolve eq9 eq3683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3683
  have eq3858 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3814
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq3814
    | exact resolve eq3814 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3814
  have eq6508 : ∀ X0 : G, (M.op X0 X0) ≠ (k (k (M.op X0 X0) X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (k (k (k (M.op X0 X0) X0) (M.op X0 X0)) (k (k (M.op X0 X0) X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq292 (M.op X0 X0)
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq292
    | exact resolve eq292 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq292
  have eq6530 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k (k (k (M.op X0 X0) X0) (M.op X0 X0)) (k (k (M.op X0 X0) X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq6508 X0
       have i₂ := eq288 X0
       grind)
    | exact superpose eq288 eq6508
    | (have j0 := eq6508 X0
       grind)
    | exact resolve eq6508 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6508
  have eq6541 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq6530 X0
       have i₂ := eq288 X0
       grind)
    | exact superpose eq288 eq6530
    | (have j0 := eq6530 X0
       grind)
    | exact resolve eq6530 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288 eq6530
  have eq6549 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq6541 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq6541 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq6541 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6541
  have eq6596 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq6549 (σ X0)
       grind)
    | exact superpose eq6549 eq13
    | exact resolve eq13 eq6549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6629 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3858
       have i₂ := eq6549 y
       grind)
    | exact superpose eq6549 eq3858
    | exact resolve eq3858 eq6549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3858
  have eq6660 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6596 X0
       have i₂ := eq6549 X0
       grind)
    | exact superpose eq6549 eq6596
    | exact resolve eq6596 eq6549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6549 eq6596
  have eq7318 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) X1
       have i₂ := eq6660 X0
       grind)
    | exact superpose eq6660 eq8
    | exact resolve eq8 eq6660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6660
  have eq7692 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq6629
       grind)
    | exact superpose eq6629 eq15
    | exact resolve eq15 eq6629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq6629
  have eq7738 : x = (M.op x y) := by grind
  clear eq7692
  have eq7863 : ∀ X0 : G, (M.op y y) = (M.op x (M.op X0 (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq2109 X0 x y
       have i₂ := eq7738
       grind)
    | exact superpose eq7738 eq2109
    | exact resolve eq2109 eq7738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2109
  have eq7865 : x = (M.op y y) := by
    first
    | (have i₁ := eq7863 x
       have i₂ := eq942 x x
       grind)
    | exact superpose eq942 eq7863
    | exact resolve eq7863 eq942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7863
  have eq17159 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq7318 y X0
       have i₂ := eq7865
       grind)
    | exact superpose eq7865 eq7318
    | exact resolve eq7318 eq7865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7318 eq7865
  have eq17623 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq942 x (σ x)
       have i₂ := eq17159 x
       grind)
    | exact superpose eq17159 eq942
    | exact resolve eq942 eq17159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942 eq17159
  have eq18082 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq17623
       grind)
    | exact superpose eq17623 eq14
    | exact resolve eq14 eq17623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17623
  have eq18108 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq18082
       have i₂ := eq7738
       grind)
    | exact superpose eq7738 eq18082
    | exact resolve eq18082 eq7738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7738 eq18082
  have eq18109 : False := by grind
  exact eq18109

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation723 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law723 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
       have i₂ := eq8 X0 X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq8 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
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
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
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
  have eq32 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 := by
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
  have eq34 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  clear eq17
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq28 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq50 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq24
  have eq102 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq39
  have eq116 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq102
    | exact resolve eq102 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq167 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq174 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq175 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (M.op (σ X0) (σ X0)) (σ X2)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq13
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq13 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 X2 X0 X1
       have i₂ := eq8 X0 X0 X1
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq305 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq235 X1 x X3
       have i₂ := eq235 X1 x X0
       grind)
    | exact superpose eq235 eq235
    | exact resolve eq235 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq314 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X1 x
       have i₂ := eq235 X1 x X0
       grind)
    | exact superpose eq235 eq8
    | exact resolve eq8 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X0 (M.op X2 X0) X2
       have i₂ := eq235 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq235 eq19
    | exact resolve eq19 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq337 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq323 X0 X1 X2
       have i₂ := eq19 X0 X0 X1
       grind)
    | exact superpose eq19 eq323
    | exact resolve eq323 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq385 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq314 X0 (M.op X0 X0)
       have i₂ := eq314 X0 X0
       grind)
    | exact superpose eq314 eq314
    | exact resolve eq314 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (M.op X0 (M.op X0 X1)) X1 X1
       have i₂ := eq314 X0 X1
       grind)
    | exact superpose eq314 eq19
    | exact resolve eq19 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq395 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 (M.op X1 (M.op X1 X0))
       have i₂ := eq314 X1 X0
       grind)
    | exact superpose eq314 eq47
    | (have j0 := eq47 X0 (M.op X1 (M.op X1 X0))
       grind)
    | (have r₁ := eq47 X1 (M.op X0 (M.op X0 X1))
       have r₂ := eq314 X0 X1
       grind)
    | exact resolve eq47 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq397 : ∀ X0 X1 : G, (k X0 (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq395 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq400 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq392 X1 X0 X2
       have i₂ := eq314 X0 X1
       grind)
    | exact superpose eq314 eq392
    | exact resolve eq392 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq446 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq385 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq385 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq385
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq385 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1 X0
       have i₂ := eq385 X0
       grind)
    | exact superpose eq385 eq19
    | exact resolve eq19 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq453 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 X0
       have i₂ := eq385 X0
       grind)
    | exact superpose eq385 eq8
    | exact resolve eq8 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq47 (M.op X0 X0) X0
       have i₂ := eq385 X0
       grind)
    | exact superpose eq385 eq47
    | (have j0 := eq47 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq47 (M.op X0 X0) X0
       have r₂ := eq385 X0
       grind)
    | exact resolve eq47 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq468 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq459 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq650 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq468 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq468 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq468
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq468 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq821 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq305 X1 (M.op X2 (M.op X0 X0)) X2
       have i₂ := eq453 X0 X2
       grind)
    | exact superpose eq453 eq305
    | exact resolve eq305 eq453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq1017 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq385 X1
       have i₂ := eq337 X1 X0 X1
       grind)
    | (have i₁ := eq385 X1
       have i₂ := eq337 X1 X1 X0
       grind)
    | exact superpose eq337 eq385
    | exact resolve eq385 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337 eq385
  have eq1137 : ∀ X0 X1 : G, (σ X0) = (k (σ (τ X1)) X1) ∨ (τ X1) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (τ X0) X0
       have i₂ := eq32 X0 X1
       grind)
    | (have i₁ := eq34 X0 X1
       have i₂ := eq32 X0 (M.op X0 (τ X1))
       grind)
    | exact superpose eq32 eq34
    | (have j1 := eq32 X1 X0
       grind)
    | exact resolve eq34 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq34
  have eq1165 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (σ X0) = (k X1 X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1137 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1137
    | (have j0 := eq1137 X0 X1
       grind)
    | exact resolve eq1137 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137
  have eq1240 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X0) (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq397 X0 (M.op X1 X0)
       have i₂ := eq1017 X1 X0
       grind)
    | exact superpose eq1017 eq397
    | exact resolve eq397 eq1017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq1313 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq400 (M.op X1 (M.op X0 X0)) X2 X1
       have i₂ := eq453 X0 X1
       grind)
    | exact superpose eq453 eq400
    | exact resolve eq400 eq453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1410 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1313 X0 X1 x
       have i₂ := eq821 X0 x X1
       grind)
    | exact superpose eq821 eq1313
    | exact resolve eq1313 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821 eq1313
  have eq1565 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq167
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq167
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq167 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1566 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1565
  have eq1921 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (τ (σ X0)) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq174 X0 X0
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq174
    | (have j0 := eq174 X1 X0
       have j1 := eq31 X1 X0
       grind)
    | exact resolve eq174 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq174
  have eq1964 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X1 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1921 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1921
    | (have j0 := eq1921 X0 X1
       grind)
    | exact resolve eq1921 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1921
  have eq3052 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq400 X1 X0 X0
       have i₂ := eq1410 (M.op X0 X1) X0
       grind)
    | exact superpose eq1410 eq400
    | exact resolve eq400 eq1410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq3057 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq453 X0 X1
       have i₂ := eq1410 X0 X1
       grind)
    | (have i₁ := eq453 X0 X0
       have i₂ := eq1410 X0 X0
       grind)
    | exact superpose eq1410 eq453
    | exact resolve eq453 eq1410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410
  have eq3516 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 (M.op X1 X0)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq314 X1 (M.op X0 (M.op X1 X0))
       have i₂ := eq3057 X0 X1
       grind)
    | exact superpose eq3057 eq314
    | exact resolve eq314 eq3057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314 eq3057
  have eq3536 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3516 X0 X1
       have i₂ := eq1017 X0 (M.op X1 X0)
       grind)
    | exact superpose eq1017 eq3516
    | exact resolve eq3516 eq1017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017 eq3516
  have eq5393 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq167
       have i₂ := eq446 y x
       grind)
    | exact superpose eq446 eq167
    | (have j1 := eq446 y x
       grind)
    | exact resolve eq167 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq5394 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq5393
  have eq6156 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k X1 X2)) = (k (M.op X0 X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq175 (τ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq175
    | exact resolve eq175 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq6308 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k X1 X2)) = (k (M.op X0 X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6156 X0 X1 X2
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq6156
    | (have j0 := eq6156 X0 X1 X2
       grind)
    | exact resolve eq6156 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq6156
  have eq8681 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq116 x
       have i₂ := eq1566
       grind)
    | exact superpose eq1566 eq116
    | exact resolve eq116 eq1566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq1566
  have eq8751 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8681
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq8681
    | exact resolve eq8681 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8681
  have eq9160 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq8751
       grind)
    | exact superpose eq8751 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq8751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8751
  have eq9165 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq9160
  have eq9338 : y = (M.op x (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3052 x y
       have i₂ := eq9165
       grind)
    | exact superpose eq9165 eq3052
    | exact resolve eq3052 eq9165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3052 eq9165
  have eq13656 : (M.op x x) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq452 x x
       have i₂ := eq9338
       grind)
    | exact superpose eq9338 eq452
    | exact resolve eq452 eq9338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9338
  have eq72291 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq468 (σ x)
       have i₂ := eq5394
       grind)
    | exact superpose eq5394 eq468
    | exact resolve eq468 eq5394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5394
  have eq72418 : (σ y) = (σ (k y x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq72291
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq72291
    | exact resolve eq72291 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72291
  have eq74226 : (k y x) = (τ (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq9 (k y x)
       have i₂ := eq72418
       grind)
    | exact superpose eq72418 eq9
    | exact resolve eq9 eq72418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72418
  have eq74333 : y = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq74226
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq74226
    | exact resolve eq74226 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74226
  have eq74341 : y = (k y x) := by
    first
    | (have j1 := eq47 y x
       grind)
    | (have r₁ := eq74333
       have r₂ := eq47 y x
       grind)
    | exact resolve eq74333 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74333
  have eq75355 : x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq74341
       grind)
    | exact superpose eq74341 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq74341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74341
  have eq76044 : x ≠ y ∨ y = (k y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq47 y y
       have i₂ := eq75355
       grind)
    | exact superpose eq75355 eq47
    | (have j0 := eq47 y y
       grind)
    | (have r₁ := eq47 y x
       have r₂ := eq75355
       grind)
    | exact resolve eq47 eq75355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq76113 : y = (k y (M.op x x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1240 y y
       have i₂ := eq75355
       grind)
    | exact superpose eq75355 eq1240
    | exact resolve eq1240 eq75355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240
  have eq118725 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (k (σ X0) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1165 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1165
    | (have j0 := eq1165 X1 (σ X0)
       grind)
    | exact resolve eq1165 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165
  have eq119535 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (k (σ X0) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq118725 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq118725
    | (have j0 := eq118725 X0 X1
       grind)
    | exact resolve eq118725 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118725
  have eq119639 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq119535 X0 X1
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq119535
    | (have j0 := eq119535 X0 X1
       grind)
    | exact resolve eq119535 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119535
  have eq121274 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq1964 y x
       grind)
    | exact superpose eq1964 eq14
    | (have j1 := eq1964 y x
       grind)
    | (have r₁ := eq14
       have r₂ := eq1964 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq1964 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq1964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1964
  have eq121888 : (σ y) = (σ (k x x)) ∨ x = y := by
    first
    | (have j1 := eq119639 x y
       grind)
    | (have r₁ := eq121274
       have r₂ := eq119639 x y
       grind)
    | (have r₁ := eq121274
       have r₂ := eq119639 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq121274
       have r₂ := eq119639 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq121274 eq119639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119639 eq121274
  have eq122223 : (k x x) = (τ (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq121888
       grind)
    | exact superpose eq121888 eq9
    | exact resolve eq9 eq121888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121888
  have eq122340 : y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq122223
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq122223
    | exact resolve eq122223 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122223
  have eq123281 : y = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq650 x x
       have i₂ := eq122340
       grind)
    | exact superpose eq122340 eq650
    | exact resolve eq650 eq122340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650 eq122340
  have eq123288 : y = (M.op x x) ∨ x = y := by grind
  clear eq123281
  have eq123552 : y = (k y y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq76113
       have i₂ := eq123288
       grind)
    | exact superpose eq123288 eq76113
    | exact resolve eq76113 eq123288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76113 eq123288
  have eq123724 : y = (k y y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq123552
       have r₂ := eq76044
       grind)
    | exact resolve eq123552 eq76044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76044 eq123552
  have eq130705 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (M.op X2 X2) (σ (τ X1))) ∨ (k X2 (σ (τ X0))) = (M.op X2 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6308 X2 (τ X0) (τ X1)
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq6308
    | (have j0 := eq6308 X2 (τ X0) X2
       grind)
    | exact resolve eq6308 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq6308
  have eq131334 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (M.op X2 X2) X1) ∨ (k X2 (σ (τ X0))) = (M.op X2 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq130705 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq130705
    | (have j0 := eq130705 X0 X1 X2
       grind)
    | exact resolve eq130705 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130705
  have eq131433 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (M.op X2 X2) X1) ∨ (k X2 (σ (τ X0))) = (M.op X2 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq131334 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq131334
    | (have j0 := eq131334 X0 X1 X2
       grind)
    | exact resolve eq131334 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131334
  have eq131455 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (k X0 X1) = (k (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq131433 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq131433
    | (have j0 := eq131433 X0 X1 X2
       grind)
    | exact resolve eq131433 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131433
  have eq144908 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq446 y y
       have i₂ := eq123724
       grind)
    | exact superpose eq123724 eq446
    | (have j0 := eq446 y y
       grind)
    | exact resolve eq446 eq123724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq123724
  have eq144911 : y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq144908
  have eq147180 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq453 y X0
       have i₂ := eq144911
       grind)
    | exact superpose eq144911 eq453
    | exact resolve eq453 eq144911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144911
  have eq178935 : y = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq147180 y
       have i₂ := eq75355
       grind)
    | exact superpose eq75355 eq147180
    | exact resolve eq147180 eq75355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75355 eq147180
  have eq179109 : y = (M.op y x) := by grind
  clear eq178935
  have eq179178 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13656
       have i₂ := eq179109
       grind)
    | exact superpose eq179109 eq13656
    | exact resolve eq13656 eq179109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13656
  have eq179272 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq3536 x y
       have i₂ := eq179109
       grind)
    | exact superpose eq179109 eq3536
    | exact resolve eq3536 eq179109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3536 eq179109
  have eq179296 : y = (M.op x x) := by grind
  clear eq179178
  have eq489915 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq468 X1
       have i₂ := eq131455 X0 X1 X1
       grind)
    | (have i₁ := eq468 X1
       have i₂ := eq131455 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq131455 eq468
    | (have j1 := eq131455 X0 X1 X1
       grind)
    | exact resolve eq468 eq131455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468 eq131455
  have eq490039 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq489915 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489915
  have eq490040 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq490039 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490039
  have eq490345 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq490040 (σ X0)
       grind)
    | exact superpose eq490040 eq13
    | exact resolve eq13 eq490040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq490710 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq490345 X0
       have i₂ := eq490040 X0
       grind)
    | exact superpose eq490040 eq490345
    | exact resolve eq490345 eq490040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490040 eq490345
  have eq491515 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq453 (σ X0) X1
       have i₂ := eq490710 X0
       grind)
    | exact superpose eq490710 eq453
    | exact resolve eq453 eq490710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq495032 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq491515 x X0
       have i₂ := eq179296
       grind)
    | exact superpose eq179296 eq491515
    | exact resolve eq491515 eq179296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179296 eq491515
  have eq495511 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq452 (σ y) (σ y)
       have i₂ := eq495032 (σ y)
       grind)
    | exact superpose eq495032 eq452
    | exact resolve eq452 eq495032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452 eq495032
  have eq495715 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq495511
       have i₂ := eq490710 y
       grind)
    | exact superpose eq490710 eq495511
    | exact resolve eq495511 eq490710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490710 eq495511
  have eq495862 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq495715
       have i₂ := eq179272
       grind)
    | exact superpose eq179272 eq495715
    | exact resolve eq495715 eq179272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179272 eq495715
  have eq495962 : False := by grind
  exact eq495962

/-- `Equation727`: `x = y ◇ (y ◇ ((z ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pyx_Equation727 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law727 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law727.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X1) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) X1 X2
       have i₂ := eq8 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq16 X0 (τ X0)
       have i₂ := eq32 (τ X0)
       grind)
    | exact superpose eq32 eq16
    | exact resolve eq16 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq37 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq36
    | exact resolve eq36 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq41 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq37
    | exact resolve eq37 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq37
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq93 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq164 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 (M.op X2 X0) x
       have i₂ := eq22 X1 X0 X2 x
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq186 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op (τ X0) (τ X0))
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq9
    | exact resolve eq9 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq435 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) X0) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq164 X2 (M.op (M.op X1 X2) X0) X3
       have i₂ := eq8 X0 X2 X1
       grind)
    | exact superpose eq8 eq164
    | exact resolve eq164 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq581 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X1 (M.op X2 (M.op X2 X0))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq435 X3 (M.op x X2) (M.op X2 (M.op X2 X0)) X1
       have i₂ := eq164 X2 X0 x
       grind)
    | exact superpose eq164 eq435
    | exact resolve eq435 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq435
  have eq859 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X3 (M.op X0 (M.op X0 X0))) X2) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq581 X1 X3 X0 X2
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq581 X0 X1 X0 X3
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq581
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq581 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq972 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X2) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq859 X0 X1 X2 x
       have i₂ := eq581 X0 x X0 X2
       grind)
    | exact superpose eq581 eq859
    | (have j0 := eq859 X0 X1 X2 x
       grind)
    | exact resolve eq859 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581 eq859
  have eq1190 : ∀ X0 X1 : G, (M.op X1 (τ X0)) ≠ (τ (M.op X0 X0)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 (τ X0) X1
       have i₂ := eq186 X0
       grind)
    | exact superpose eq186 eq93
    | (have j0 := eq93 (τ X0) X1
       grind)
    | exact resolve eq93 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq5197 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (M.op X1 X1)) ∨ (M.op X0 (τ X1)) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq186 X1
       have i₂ := eq972 (τ X1) X0 (τ X1)
       grind)
    | (have i₁ := eq186 X0
       have i₂ := eq972 X0 (τ X0) (τ X0)
       grind)
    | exact superpose eq972 eq186
    | (have j1 := eq972 (τ X1) X0 x
       grind)
    | exact resolve eq186 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq972
  have eq5358 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq5197 X0 X1
       have j1 := eq1190 X1 X0
       grind)
    | (have r₁ := eq5197 X1 X0
       have r₂ := eq1190 X0 X1
       grind)
    | exact resolve eq5197 eq1190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190 eq5197
  have eq5656 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5358 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq5358
    | exact resolve eq5358 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5358
  have eq6105 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq5656 (σ X1) (σ X0)
       grind)
    | exact superpose eq5656 eq13
    | exact resolve eq13 eq5656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6123 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6105 X0 X1
       have i₂ := eq5656 X1 X0
       grind)
    | exact superpose eq5656 eq6105
    | exact resolve eq6105 eq5656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5656 eq6105
  have eq8827 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq6123 x y
       grind)
    | exact superpose eq6123 eq14
    | (have r₁ := eq14
       have r₂ := eq6123 x y
       grind)
    | exact resolve eq14 eq6123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6123
  have eq8899 : False := by grind
  exact eq8899
