import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation916`: `x = y ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_x_pxy_Equation916 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law916 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law916.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = X0 := by
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
  have eq21 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq8 (M.op X0 X0) (M.op X0 X0)
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
  have eq30 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X1 (M.op (M.op X1 X1) (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op (M.op X1 X1) (M.op X0 X0))
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 X1 (M.op (M.op X1 X1) (M.op X0 X0))
       grind)
    | (have r₁ := eq11 X1 (M.op (M.op X1 X1) (M.op (M.op X1 X1) (M.op X1 X1)))
       have r₂ := eq8 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X2 X2) (M.op X0 X1))) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X2
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X1 X1
       have i₂ := eq12 X1 X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = X0 ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0
       have i₂ := eq12 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 (M.op X1 X1) (M.op X0 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 (M.op X0 X0) X1
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
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
  have eq49 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq53 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq50
    | exact resolve eq50 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq50 X0 (τ X1)
       grind)
    | exact superpose eq50 eq16
    | (have j1 := eq50 X0 (τ X1)
       grind)
    | exact resolve eq16 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq89 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq21 (M.op X0 X0)
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X0 X0) X1
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0)
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 : G, (k X0 (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) = X0 := by
    intro X0
    first
    | (have j0 := eq30 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq104 : ∀ X0 : G, (k X0 (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq103 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq103
    | exact resolve eq103 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq105 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 (M.op (M.op X1 X1) (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq70 X1 (M.op (M.op X1 X1) (M.op X0 X0))
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq70
    | (have j0 := eq70 X1 (M.op (M.op X1 X1) (M.op X0 X0))
       grind)
    | (have r₁ := eq70 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq8 X0 X0
       grind)
    | exact resolve eq70 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq70 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq70
    | (have j0 := eq70 X0 (M.op X0 (M.op X0 X0))
       grind)
    | (have r₁ := eq70 X0 (M.op X0 (M.op X0 X0))
       have r₂ := eq91 X0
       grind)
    | exact resolve eq70 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (k X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq106 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq138 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (M.op (σ X0) (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq27 X0 (M.op (σ X0) (M.op (σ X0) (σ X0)))
       have i₂ := eq110 (σ X0)
       grind)
    | exact superpose eq110 eq27
    | exact resolve eq27 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq110
  have eq142 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (M.op (σ X0) (σ X0))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq138 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq138
    | exact resolve eq138 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq496 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq701 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq94 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq8 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
       grind)
    | exact superpose eq8 eq94
    | exact resolve eq94 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq720 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 X1) (M.op X0 X0))) = X2 ∨ (M.op X0 X0) = (k X2 (M.op (M.op X2 X2) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41 X1 (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0))) X2
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq41
    | exact resolve eq41 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq727 : ∀ X0 X2 : G, (M.op X0 X0) = (k X2 (M.op (M.op X2 X2) (M.op X0 (M.op X0 X0)))) ∨ X0 = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq720 X0 x X2
       have i₂ := eq8 X0 x
       grind)
    | exact superpose eq8 eq720
    | (have j0 := eq720 X0 x X2
       grind)
    | exact resolve eq720 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq733 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq701 X0
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq701
    | exact resolve eq701 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq739 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq733 X0
       have i₂ := eq21 (M.op X0 X0)
       grind)
    | exact superpose eq21 eq733
    | exact resolve eq733 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq742 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq739 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq739
    | exact resolve eq739 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739
  have eq750 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq742 (M.op X0 X0)
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq742
    | exact resolve eq742 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq758 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq44 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq742 X0
       grind)
    | exact superpose eq742 eq44
    | exact resolve eq44 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq770 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq750 X0
       have i₂ := eq742 X0
       grind)
    | exact superpose eq742 eq750
    | exact resolve eq750 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq776 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq95 (M.op X0 X0) X1
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq95
    | exact resolve eq95 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq794 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq94 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq95 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq95 eq94
    | exact resolve eq94 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq806 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq794 X0
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq794
    | exact resolve eq794 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq810 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq776 X0 X1
       have i₂ := eq742 X0
       grind)
    | exact superpose eq742 eq776
    | exact resolve eq776 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq839 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq69
    | exact resolve eq69 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq872 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq839 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq839
    | (have j0 := eq839 X0 X1
       grind)
    | exact resolve eq839 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq885 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq806 X0
       grind)
    | exact superpose eq806 eq8
    | exact resolve eq8 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq895 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0
    first
    | (have i₁ := eq91 (M.op X0 (M.op X0 X0))
       have i₂ := eq806 X0
       grind)
    | exact superpose eq806 eq91
    | exact resolve eq91 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq924 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq895 X0
       have i₂ := eq770 X0
       grind)
    | exact superpose eq770 eq895
    | exact resolve eq895 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq942 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq64 x y
       grind)
    | exact superpose eq64 eq14
    | (have j1 := eq64 x y
       grind)
    | exact resolve eq14 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq967 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       have j1 := eq64 X0 X1
       grind)
    | exact resolve eq11 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq977 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq967 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq967
    | (have j0 := eq967 X0 X1
       grind)
    | exact resolve eq967 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967
  have eq978 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq977 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq1030 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X1 X1)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq810 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq810 X0 X0
       grind)
    | exact superpose eq810 eq810
    | exact resolve eq810 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1073 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) = X0 ∨ (k (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))
       have i₂ := eq810 X0 X1
       grind)
    | exact superpose eq810 eq12
    | exact resolve eq12 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1081 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 (M.op X1 X1))) = X0 ∨ (k (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1073 X0 X1
       have i₂ := eq89 X1
       grind)
    | exact superpose eq89 eq1073
    | (have j0 := eq1073 X0 X1
       grind)
    | exact resolve eq1073 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073
  have eq1107 : ∀ X0 X1 : G, (k (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X0 X0))) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1081 X0 X1
       have i₂ := eq742 X1
       grind)
    | exact superpose eq742 eq1081
    | (have j0 := eq1081 X0 X1
       grind)
    | exact resolve eq1081 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081
  have eq1172 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = (M.op X2 (M.op (M.op X2 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq885 X1 X2
       have i₂ := eq885 X1 X0
       grind)
    | exact superpose eq885 eq885
    | exact resolve eq885 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1195 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op (M.op X0 X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq91 X1
       have i₂ := eq885 X1 X0
       grind)
    | exact superpose eq885 eq91
    | exact resolve eq91 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1196 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op (M.op X2 X2) (M.op X0 (M.op (M.op X0 X0) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq94 X1 X2
       have i₂ := eq885 X1 X0
       grind)
    | exact superpose eq885 eq94
    | exact resolve eq94 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq1203 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) (M.op X1 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq810 X1 X2
       have i₂ := eq885 X1 X0
       grind)
    | exact superpose eq885 eq810
    | exact resolve eq810 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1218 : ∀ X0 X1 : G, (k X1 (τ (M.op X0 (M.op (M.op X0 X0) (σ X1))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq142 X1
       have i₂ := eq885 (σ X1) X0
       grind)
    | exact superpose eq885 eq142
    | exact resolve eq142 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq1278 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq49
    | exact resolve eq49 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1384 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1278 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1278
    | (have j0 := eq1278 X0 X1
       grind)
    | exact resolve eq1278 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278
  have eq1398 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1195 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq810 X0 X0
       grind)
    | exact superpose eq810 eq1195
    | exact resolve eq1195 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1419 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1195 x (M.op X0 X0)
       have i₂ := eq8 X0 x
       grind)
    | exact superpose eq8 eq1195
    | exact resolve eq1195 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195
  have eq2708 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1398 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq1398 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq1398
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq1398 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398
  have eq2806 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2708 X0 X1
       have i₂ := eq924 X0
       grind)
    | exact superpose eq924 eq2708
    | (have j0 := eq2708 X0 X1
       grind)
    | exact resolve eq2708 eq924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924 eq2708
  have eq3242 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq496 (τ X0) (τ X1)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq496
    | (have j0 := eq496 (τ X0) (τ X1)
       grind)
    | exact resolve eq496 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq3268 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3242 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3242
    | (have j0 := eq3242 X0 X1
       grind)
    | exact resolve eq3242 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3242
  have eq3273 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3268 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq3268
    | (have j0 := eq3268 X0 X1
       grind)
    | exact resolve eq3268 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3268
  have eq3276 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3273 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3273
    | (have j0 := eq3273 X0 X1
       grind)
    | exact resolve eq3273 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3273
  have eq3277 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3276 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3276
    | (have j0 := eq3276 X0 X1
       grind)
    | exact resolve eq3276 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3276
  have eq3544 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X0)) X1) ≠ X0 ∨ (M.op (M.op X0 (M.op X0 X0)) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3277 (M.op X1 (M.op X1 X1)) X1
       have i₂ := eq810 X1 X1
       grind)
    | exact superpose eq810 eq3277
    | exact resolve eq3277 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810 eq3277
  have eq4834 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0))) = (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1030 (M.op X1 X0) (M.op X1 (M.op X1 X1))
       have i₂ := eq1030 X0 X1
       grind)
    | exact superpose eq1030 eq1030
    | exact resolve eq1030 eq1030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5107 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0))) = (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 (M.op X1 X1)))) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4834 X0 X1
       have i₂ := eq89 X1
       grind)
    | exact superpose eq89 eq4834
    | exact resolve eq4834 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq4834
  have eq5220 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0))) = (M.op (M.op (M.op X1 (M.op X1 X1)) X1) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5107 X0 X1
       have i₂ := eq742 X1
       grind)
    | exact superpose eq742 eq5107
    | exact resolve eq5107 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5107
  have eq5267 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5220 X0 X1
       have i₂ := eq770 X1
       grind)
    | exact superpose eq770 eq5220
    | exact resolve eq5220 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5220
  have eq12505 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq942
       have i₂ := eq872 y x
       grind)
    | exact superpose eq872 eq942
    | (have j1 := eq872 y x
       grind)
    | (have r₁ := eq942
       have r₂ := eq872 y x
       grind)
    | exact resolve eq942 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872 eq942
  have eq12506 : (σ (M.op x y)) = (σ x) ∨ x = (k x y) := by grind
  clear eq12505
  have eq12576 : (M.op x y) = (τ (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq12506
       grind)
    | exact superpose eq12506 eq9
    | exact resolve eq9 eq12506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12506
  have eq12631 : x = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12576
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq12576
    | exact resolve eq12576 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12576
  have eq12632 : x = (k x y) := by
    first
    | (have j1 := eq70 x y
       grind)
    | (have r₁ := eq12631
       have r₂ := eq70 x y
       grind)
    | exact resolve eq12631 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq12631
  have eq18687 : ∀ X0 X1 : G, (k (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op (M.op X0 X0) (M.op X1 X1))) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1107 X1 (M.op X0 X0)
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq1107
    | (have j0 := eq1107 (k (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op (M.op X0 X0) (M.op X1 X1))) X1
       grind)
    | exact resolve eq1107 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq18863 : ∀ X0 X1 : G, (k X0 (M.op (M.op X0 X0) (M.op X1 X1))) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18687 X0 X1
       have i₂ := eq742 X0
       grind)
    | exact superpose eq742 eq18687
    | (have j0 := eq18687 X0 X1
       grind)
    | exact resolve eq18687 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq18687
  have eq27388 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 (M.op X1 X1)) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1030 (M.op X1 (M.op X1 X1)) X0
       have i₂ := eq2806 X1 X0
       grind)
    | exact superpose eq2806 eq1030
    | (have j1 := eq2806 X1 X0
       grind)
    | exact resolve eq1030 eq2806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2806
  have eq27507 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 X1) (M.op (M.op X1 X1) (M.op (M.op X1 X1) (M.op X1 X1)))) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq27388 X0 X1
       have i₂ := eq5267 (M.op X1 X1) X1
       grind)
    | exact superpose eq5267 eq27388
    | (have j0 := eq27388 X0 X1
       grind)
    | exact resolve eq27388 eq5267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5267 eq27388
  have eq27666 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X0)) X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq27507 X0 X1
       have i₂ := eq91 (M.op X1 X1)
       grind)
    | exact superpose eq91 eq27507
    | (have j0 := eq27507 X0 X1
       grind)
    | exact resolve eq27507 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27507
  have eq27714 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq27666 X0 X1
       have i₂ := eq770 X0
       grind)
    | exact superpose eq770 eq27666
    | (have j0 := eq27666 X0 X1
       grind)
    | exact resolve eq27666 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27666
  have eq28513 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X1) X2)) (M.op X2 (M.op X0 X0))) = X3 ∨ (M.op X0 X3) = (k X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1203 X1 X2 X3
       have i₂ := eq27714 X3 X0
       grind)
    | (have i₁ := eq1203 X0 X1 X1
       have i₂ := eq27714 X0 X1
       grind)
    | exact superpose eq27714 eq1203
    | (have j1 := eq27714 X3 X0
       grind)
    | exact resolve eq1203 eq27714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27714
  have eq28864 : ∀ X0 X3 : G, (M.op X0 X3) = (k X0 X3) ∨ X0 = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq28513 X0 x x X3
       have i₂ := eq1203 x x X0
       grind)
    | exact superpose eq1203 eq28513
    | (have j0 := eq28513 X0 x x X3
       grind)
    | exact resolve eq28513 eq1203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203 eq28513
  have eq29351 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq28864 (σ X0) (σ X1)
       grind)
    | exact superpose eq28864 eq13
    | (have j1 := eq28864 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq13 eq28864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29374 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12632
       have i₂ := eq28864 x y
       grind)
    | exact superpose eq28864 eq12632
    | (have j1 := eq28864 x (M.op x y)
       grind)
    | exact resolve eq12632 eq28864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28864
  have eq30188 : (M.op y (M.op y y)) = (M.op (M.op x (M.op x x)) x) ∨ x = y := by
    first
    | (have i₁ := eq1030 y x
       have i₂ := eq29374
       grind)
    | exact superpose eq29374 eq1030
    | exact resolve eq1030 eq29374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030 eq29374
  have eq30203 : (M.op x x) = (M.op y (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq30188
       have i₂ := eq770 x
       grind)
    | exact superpose eq770 eq30188
    | exact resolve eq30188 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770 eq30188
  have eq31434 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq978 (τ X1) (τ X0)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq978
    | exact resolve eq978 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978
  have eq31491 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq31434 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq31434
    | (have j0 := eq31434 X0 X1
       grind)
    | exact resolve eq31434 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31434
  have eq31495 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq31491 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq31491
    | (have j0 := eq31491 X0 X1
       grind)
    | exact resolve eq31491 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31491
  have eq31497 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31495 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq31495
    | (have j0 := eq31495 X0 X1
       grind)
    | exact resolve eq31495 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31495
  have eq31498 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31497 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq31497
    | (have j0 := eq31497 X0 X1
       grind)
    | exact resolve eq31497 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31497
  have eq36486 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31498 x (M.op (M.op x x) (M.op X0 (M.op X0 X0)))
       have i₂ := eq727 X0 x
       grind)
    | exact superpose eq727 eq31498
    | (have j1 := eq727 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq31498 x (M.op (M.op x x) (M.op x (M.op x x)))
       have r₂ := eq727 x x
       grind)
    | (have r₁ := eq31498 X0 X1
       have r₂ := eq727 (M.op X0 X0) (k X0 X1)
       grind)
    | (have r₁ := eq31498 X0 X1
       have r₂ := eq727 (k X0 X1) (M.op X0 X0)
       grind)
    | exact resolve eq31498 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq36493 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq31498 (M.op X0 X0) (M.op X0 (M.op X0 X0))
       have i₂ := eq758 X0
       grind)
    | exact superpose eq758 eq31498
    | (have j1 := eq758 X0
       grind)
    | exact resolve eq31498 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq36522 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) ≠ (τ (k X0 X1)) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31498 (τ X1) (τ X0)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq31498
    | exact resolve eq31498 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq31498
  have eq36530 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq36493 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36493
  have eq36548 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq36530 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq36530
    | (have j0 := eq36530 X0
       grind)
    | exact resolve eq36530 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq36530
  have eq37379 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X1)) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq36548 X1
       have i₂ := eq885 X1 X0
       grind)
    | exact superpose eq885 eq36548
    | (have j0 := eq36548 X1
       grind)
    | exact resolve eq36548 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885 eq36548
  have eq39748 : y = (k y (M.op (M.op y y) (M.op x x))) ∨ x = y := by
    first
    | (have i₁ := eq104 y
       have i₂ := eq30203
       grind)
    | exact superpose eq30203 eq104
    | exact resolve eq104 eq30203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq30203
  have eq39861 : y = (k y (M.op (M.op y y) (M.op x x))) := by
    first
    | (have j1 := eq105 x y
       grind)
    | (have r₁ := eq39748
       have r₂ := eq105 y (k y (M.op (M.op y y) (M.op x x)))
       grind)
    | (have r₁ := eq39748
       have r₂ := eq105 (k y (M.op (M.op y y) (M.op x x))) y
       grind)
    | (have r₁ := eq39748
       have r₂ := eq105 x y
       grind)
    | exact resolve eq39748 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq39748
  have eq40235 : (σ y) = (σ (M.op y (M.op (M.op y y) (M.op x x)))) ∨ (M.op y y) = (M.op y (M.op (M.op y y) (M.op x x))) := by
    first
    | (have i₁ := eq1384 (M.op (M.op y y) (M.op x x)) y
       have i₂ := eq39861
       grind)
    | exact superpose eq39861 eq1384
    | (have j0 := eq1384 (M.op (M.op y y) (M.op x x)) y
       grind)
    | exact resolve eq1384 eq39861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384 eq39861
  have eq40244 : (σ x) = (σ y) ∨ (M.op y y) = (M.op y (M.op (M.op y y) (M.op x x))) := by
    first
    | (have i₁ := eq40235
       have i₂ := eq8 x y
       grind)
    | exact superpose eq8 eq40235
    | exact resolve eq40235 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40235
  have eq40277 : x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq40244
       have i₂ := eq8 x y
       grind)
    | exact superpose eq8 eq40244
    | exact resolve eq40244 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40244
  have eq41585 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1419 y
       have i₂ := eq40277
       grind)
    | exact superpose eq40277 eq1419
    | exact resolve eq1419 eq40277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1419 eq40277
  have eq272295 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq29351 x y
       grind)
    | exact superpose eq29351 eq14
    | (have j1 := eq29351 x y
       grind)
    | exact resolve eq14 eq29351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29351
  have eq272304 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq272295
       have i₂ := eq12632
       grind)
    | exact superpose eq12632 eq272295
    | exact resolve eq272295 eq12632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12632 eq272295
  have eq272308 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq272304
       have i₂ := eq41585
       grind)
    | exact superpose eq41585 eq272304
    | exact resolve eq272304 eq41585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41585 eq272304
  have eq272320 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq272308
  have eq272321 : (σ x) = (σ y) := by grind
  clear eq272320
  have eq272325 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq272321
       grind)
    | exact superpose eq272321 eq9
    | exact resolve eq9 eq272321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272321
  have eq272399 : x = y := by
    first
    | (have i₁ := eq272325
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq272325
    | exact resolve eq272325 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272325
  have eq272403 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq272399
       grind)
    | exact superpose eq272399 eq14
    | exact resolve eq14 eq272399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272399
  have eq304788 : ∀ X0 X1 : G, (τ X0) ≠ (M.op (τ X1) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq36522 X0 (M.op (M.op X0 X0) (M.op X1 X1))
       have i₂ := eq18863 X0 X1
       grind)
    | exact superpose eq18863 eq36522
    | (have j1 := eq18863 X1 X0
       grind)
    | (have r₁ := eq36522 X0 X1
       have r₂ := eq18863 (τ X0) (τ (k X0 X1))
       grind)
    | exact resolve eq36522 eq18863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18863 eq36522
  have eq313420 : ∀ X0 X1 : G, (M.op (τ X1) (τ X1)) ≠ X0 ∨ (τ X1) = X0 ∨ (M.op X1 X1) = (σ X0) := by
    intro X0 X1
    first
    | (have i₁ := eq304788 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq304788
    | (have j0 := eq304788 (σ X0) X1
       grind)
    | (have r₁ := eq304788 (σ (M.op (τ X1) (τ X1))) X1
       have r₂ := eq9 (M.op (τ X1) (τ X1))
       grind)
    | exact resolve eq304788 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304788
  have eq313423 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ X0 = X1 ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq313420 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq313420
    | (have j0 := eq313420 X1 (σ X0)
       grind)
    | (have r₁ := eq313420 (τ (σ (M.op (τ X1) (τ X1)))) X1
       have r₂ := eq9 (M.op (τ X1) (τ X1))
       grind)
    | exact resolve eq313420 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313420
  have eq313430 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq313423 (M.op (σ X0) (σ X0)) (σ (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313423
  have eq313443 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq272403
       have i₂ := eq313430 x
       grind)
    | exact superpose eq313430 eq272403
    | (have j1 := eq313430 x
       grind)
    | (have r₁ := eq272403
       have r₂ := eq313430 x
       grind)
    | exact resolve eq272403 eq313430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313430
  have eq313453 : x = (M.op x x) := by grind
  clear eq313443
  have eq313839 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = (M.op x (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1172 X0 X1 x
       have i₂ := eq313453
       grind)
    | exact superpose eq313453 eq1172
    | exact resolve eq1172 eq313453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq313855 : ∀ X0 : G, (k X0 (τ (M.op x (M.op x (σ X0))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1218 x X0
       have i₂ := eq313453
       grind)
    | exact superpose eq313453 eq1218
    | exact resolve eq1218 eq313453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218
  have eq313907 : ∀ X0 : G, x ≠ (k (M.op x x) X0) ∨ x = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq3544 x x
       have i₂ := eq313453
       grind)
    | exact superpose eq313453 eq3544
    | exact resolve eq3544 eq313453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3544
  have eq314012 : ∀ X0 : G, (M.op X0 X0) ≠ x ∨ x = X0 ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq36486 x x
       have i₂ := eq313453
       grind)
    | exact superpose eq313453 eq36486
    | (have j0 := eq36486 x X0
       grind)
    | exact resolve eq36486 eq313453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36486
  have eq314017 : ∀ X0 : G, (M.op x (M.op x X0)) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq37379 x X0
       have i₂ := eq313453
       grind)
    | exact superpose eq313453 eq37379
    | (have j0 := eq37379 X0 X0
       grind)
    | exact resolve eq37379 eq313453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37379
  have eq314204 : ∀ X0 : G, (M.op X0 X0) ≠ x ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq314012 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314012
  have eq314287 : ∀ X0 : G, x ≠ (k x X0) ∨ x = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq313907 X0
       have i₂ := eq313453
       grind)
    | exact superpose eq313453 eq313907
    | (have j0 := eq313907 X0
       grind)
    | exact resolve eq313907 eq313453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313907
  have eq314392 : ∀ X0 : G, x ≠ (k x X0) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq314287 X0
       have i₂ := eq313453
       grind)
    | exact superpose eq313453 eq314287
    | (have j0 := eq314287 X0
       grind)
    | exact resolve eq314287 eq313453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314287
  have eq314443 : ∀ X0 X1 X2 : G, x ≠ (M.op X0 (M.op (M.op X0 X0) (M.op X1 (M.op (M.op X1 X1) X2)))) ∨ x = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq314204 X2
       have i₂ := eq1196 X1 X2 X0
       grind)
    | exact superpose eq1196 eq314204
    | (have j0 := eq314204 X2
       grind)
    | exact resolve eq314204 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196 eq314204
  have eq314526 : ∀ X1 X2 : G, x ≠ (M.op x (M.op x (M.op X1 (M.op (M.op X1 X1) X2)))) ∨ x = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq314443 x X1 X2
       have i₂ := eq313839 x (M.op X1 (M.op (M.op X1 X1) X2))
       grind)
    | exact superpose eq313839 eq314443
    | (have j0 := eq314443 x X1 X2
       grind)
    | exact resolve eq314443 eq313839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314443
  have eq314529 : ∀ X2 : G, x ≠ (M.op x (M.op x (M.op x (M.op x X2)))) ∨ x = X2 := by
    intro X2
    first
    | (have i₁ := eq314526 x X2
       have i₂ := eq313839 x X2
       grind)
    | exact superpose eq313839 eq314526
    | (have j0 := eq314526 x X2
       grind)
    | exact resolve eq314526 eq313839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313839 eq314526
  have eq315721 : x ≠ x ∨ x = (M.op x (τ (M.op x (M.op x (σ x))))) := by
    first
    | (have i₁ := eq314392 (τ (M.op x (M.op x (σ x))))
       have i₂ := eq313855 x
       grind)
    | exact superpose eq313855 eq314392
    | (have j0 := eq314392 (τ (M.op x (M.op x (σ x))))
       grind)
    | (have r₁ := eq314392 (τ (M.op x (M.op x (σ x))))
       have r₂ := eq313855 x
       grind)
    | exact resolve eq314392 eq313855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313855 eq314392
  have eq315727 : x = (M.op x (τ (M.op x (M.op x (σ x))))) := by grind
  clear eq315721
  have eq321271 : x ≠ (M.op x (M.op x (M.op x x))) ∨ x = (τ (M.op x (M.op x (σ x)))) := by
    first
    | (have i₁ := eq314529 (τ (M.op x (M.op x (σ x))))
       have i₂ := eq315727
       grind)
    | exact superpose eq315727 eq314529
    | (have j0 := eq314529 (τ (M.op x (M.op x (σ x))))
       grind)
    | exact resolve eq314529 eq315727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314529 eq315727
  have eq321319 : x = (τ (M.op x (M.op x (σ x)))) := by
    first
    | (have r₁ := eq321271
       have r₂ := eq91 x
       grind)
    | exact resolve eq321271 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq321271
  have eq321333 : (σ x) = (M.op x (M.op x (σ x))) := by
    first
    | (have i₁ := eq10 (M.op x (M.op x (σ x)))
       have i₂ := eq321319
       grind)
    | exact superpose eq321319 eq10
    | exact resolve eq10 eq321319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321319
  have eq321487 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq314017 (σ x)
       have i₂ := eq321333
       grind)
    | exact superpose eq321333 eq314017
    | (have j0 := eq314017 (σ x)
       grind)
    | (have r₁ := eq314017 (σ x)
       have r₂ := eq321333
       grind)
    | exact resolve eq314017 eq321333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314017 eq321333
  have eq321534 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq321487
  have eq321597 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq272403
       have i₂ := eq321534
       grind)
    | exact superpose eq321534 eq272403
    | exact resolve eq272403 eq321534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272403 eq321534
  have eq322149 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq321597
       have i₂ := eq313453
       grind)
    | exact superpose eq313453 eq321597
    | exact resolve eq321597 eq313453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313453 eq321597
  have eq322150 : False := by grind
  exact eq322150

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation960 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
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
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq118 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq122 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq118 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq118 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq118 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq118 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq138 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq122 (σ X0) (σ X1)
       grind)
    | exact superpose eq122 eq13
    | exact resolve eq13 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq138 X0 X1
       have i₂ := eq122 X0 X1
       grind)
    | exact superpose eq122 eq138
    | exact resolve eq138 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq138
  have eq1251 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq145 x y
       grind)
    | exact superpose eq145 eq14
    | (have r₁ := eq14
       have r₂ := eq145 x y
       grind)
    | exact resolve eq14 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq1283 : False := by grind
  exact eq1283

/-- `Equation978`: `x = y ◇ ((z ◇ z) ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_pxx_pxy_Equation978 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law978 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law978.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X2) (M.op X0 X1))) = X0 := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) (M.op (M.op X3 X3) X0)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op (M.op X1 X1) (M.op X0 X2)) X3
       have i₂ := eq8 X0 X2 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op X1 X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X2 X2) (M.op X0 (M.op X1 X1)) X1
       have i₂ := eq8 X0 (M.op X1 X1) X2
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
  have eq40 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X2) = (k X0 X2) := by
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
  have eq41 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X2 X1))) = X2 ∨ (M.op X0 X3) = (k X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X1 X0
       have i₂ := eq12 X0 X3
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X3
       grind)
    | exact resolve eq8 eq12
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
  have eq48 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq40 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq70 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 x x X0
       have i₂ := eq22 x x X1
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) X0) = X2 ∨ (M.op X2 X3) = (k X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X2 X3
       have i₂ := eq22 X0 X1 X2
       grind)
    | exact superpose eq22 eq12
    | (have j0 := eq12 X2 X3
       grind)
    | exact resolve eq12 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) X0) ≠ X2 ∨ (M.op (M.op X0 (M.op X1 X1)) X0) = (k X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 X2 X1
       have i₂ := eq22 X0 X1 X2
       grind)
    | exact superpose eq22 eq11
    | (have r₁ := eq11 (M.op (M.op X0 (M.op X1 X1)) X0) X1
       have r₂ := eq22 X0 X1 (M.op (M.op X0 (M.op X1 X1)) X0)
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X1 (M.op X1 X1)
       have i₂ := eq22 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X3 X3)) = (M.op X1 (M.op (M.op X2 X2) (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X1 (M.op X3 X3)) X1 X2
       have i₂ := eq22 X1 X3 X0
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq81 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) ≠ X2 ∨ (M.op (M.op X0 (M.op X1 X1)) X0) = (k X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq72 X0 X1 X2 X3
       have i₂ := eq76 X1 X0
       grind)
    | exact superpose eq76 eq72
    | (have j0 := eq72 X0 X1 X2 X3
       grind)
    | (have r₁ := eq72 (M.op X0 X0) X1 (M.op (M.op X0 X0) (M.op X1 X1)) X3
       have r₂ := eq76 X0 (M.op (M.op X0 X0) (M.op X1 X1))
       grind)
    | (have r₁ := eq72 X0 X1 (M.op (M.op (M.op X0 (M.op X1 X1)) X0) (M.op X0 X0)) X3
       have r₂ := eq76 X0 (M.op (M.op X0 (M.op X1 X1)) X0)
       grind)
    | exact resolve eq72 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq82 : ∀ X0 X2 X3 : G, (M.op X0 X0) = X2 ∨ (M.op X2 X3) = (k X2 X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq71 X0 x X2 X3
       have i₂ := eq76 x X0
       grind)
    | exact superpose eq76 eq71
    | (have j0 := eq71 X0 x X2 X3
       grind)
    | exact resolve eq71 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq89 : ∀ X0 X2 X3 : G, (M.op X0 X0) ≠ X2 ∨ (M.op X0 X0) = (k X2 X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq81 X0 x X2 X3
       have i₂ := eq76 x X0
       grind)
    | exact superpose eq76 eq81
    | (have j0 := eq81 X0 x X2 X3
       grind)
    | (have r₁ := eq81 (M.op X0 X0) x (M.op X0 X0) X3
       have r₂ := eq76 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq81 X0 x (M.op (M.op X0 X0) (M.op X0 X0)) X3
       have r₂ := eq76 X0 (M.op X0 X0)
       grind)
    | exact resolve eq81 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq124 : ∀ X0 X1 X2 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op (σ X0) X2) = (k (σ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq48 (σ X0) (σ X1) X2
       grind)
    | exact superpose eq48 eq13
    | (have j1 := eq48 (σ X0) X1 X2
       grind)
    | exact resolve eq13 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X0) X1) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq48 X0 (τ X1) X2
       grind)
    | exact superpose eq48 eq16
    | (have j1 := eq48 (σ X0) X1 X2
       grind)
    | exact resolve eq16 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0) X1
       have i₂ := eq76 X0 (M.op X0 X0)
       grind)
    | exact superpose eq76 eq11
    | (have r₁ := eq11 (M.op X0 X0) X1
       have r₂ := eq76 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X2) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 (M.op X1 X1) X2
       have i₂ := eq76 X1 X0
       grind)
    | exact superpose eq76 eq8
    | exact resolve eq8 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq149 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq173 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X4) X3) = (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X5 X5) (M.op (M.op X2 X2) (M.op X3 X0)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq21 (M.op (M.op X2 X2) (M.op X3 X0)) X1 (M.op (M.op X4 X4) X3) X5
       have i₂ := eq21 X3 X2 X0 X4
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X4 X4) X3) = (M.op (M.op (M.op X1 X1) X0) (M.op X3 X0)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq173 X0 X1 x X3 X4 x
       have i₂ := eq154 (M.op X3 X0) x x
       grind)
    | exact superpose eq154 eq173
    | exact resolve eq173 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq242 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X4) (M.op X2 X0)) = (M.op (M.op (M.op X1 X1) X2) (M.op X3 X0)) ∨ (M.op X3 X5) = (k X3 X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq41 X3 (M.op (M.op X1 X1) X2) (M.op (M.op X4 X4) (M.op X2 X0)) X5
       have i₂ := eq21 X2 X4 X0 X1
       grind)
    | exact superpose eq21 eq41
    | (have j0 := eq41 X3 X1 X2 X5
       grind)
    | exact resolve eq41 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq286 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq135 X0 (M.op X1 X1)
       have i₂ := eq76 X1 X0
       grind)
    | exact superpose eq76 eq135
    | (have j0 := eq135 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq135 X1 (M.op X0 X0)
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq135 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq135 X1 X1
       have i₂ := eq70 X1 X0
       grind)
    | (have i₁ := eq135 X1 X1
       have i₂ := eq70 X0 X1
       grind)
    | exact superpose eq70 eq135
    | (have j0 := eq135 X1 X1
       grind)
    | (have r₁ := eq135 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq70 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq135 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq70 X0 (M.op X0 X0)
       grind)
    | exact resolve eq135 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq295 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq286 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq354 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op X1 X1)
       have i₂ := eq295 (σ X0) X1
       grind)
    | exact superpose eq295 eq28
    | exact resolve eq28 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq357 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq354 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq354
    | exact resolve eq354 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq419 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X0
       have i₂ := eq70 (σ X0) X1
       grind)
    | (have i₁ := eq44 X0 X0
       have i₂ := eq70 X0 (σ X0)
       grind)
    | exact superpose eq70 eq44
    | exact resolve eq44 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq428 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq448 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X1) (M.op (M.op X2 X2) (σ (k X0 X1)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (σ X0) (σ X1) X2
       have i₂ := eq44 X0 X1
       grind)
    | exact superpose eq44 eq8
    | (have j1 := eq44 X0 X1
       grind)
    | exact resolve eq8 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq468 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq44 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq498 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (τ (M.op X1 X1))
       have i₂ := eq357 (σ X0) X1
       grind)
    | exact superpose eq357 eq28
    | exact resolve eq28 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq501 : ∀ X0 X1 : G, (k X0 (τ (τ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq498 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq498
    | exact resolve eq498 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq625 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (τ (τ (M.op X1 X1)))
       have i₂ := eq501 (σ X0) X1
       grind)
    | exact superpose eq501 eq28
    | exact resolve eq28 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq501
  have eq628 : ∀ X0 X1 : G, (k X0 (τ (τ (τ (M.op X1 X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq625 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq625
    | exact resolve eq625 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq633 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (M.op (τ X0) X2) = (k (τ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq127 (τ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq127
    | (have j0 := eq127 (τ X0) X1 X2
       grind)
    | exact resolve eq127 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq1050 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq154 (M.op (M.op X1 X1) X0) X3 x
       have i₂ := eq154 X0 x X1
       grind)
    | exact superpose eq154 eq154
    | exact resolve eq154 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1362 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) (M.op (M.op X1 X1) (M.op X2 X2))) ∨ (k (M.op X0 X0) X3) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) (M.op X2 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 (M.op X3 X3) X1
       have i₂ := eq77 X0 (M.op X3 X3) X2 X3
       grind)
    | (have i₁ := eq11 (M.op (M.op X2 X2) (M.op X0 X0)) X1
       have i₂ := eq77 X0 (M.op (M.op X2 X2) (M.op X0 X0)) X2 X3
       grind)
    | exact superpose eq77 eq11
    | exact resolve eq11 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1520 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) ≠ (M.op X0 X0) ∨ (k (M.op X0 X0) X3) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) (M.op X2 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1362 X0 X1 X2 X3
       have i₂ := eq154 (M.op X2 X2) X0 X1
       grind)
    | exact superpose eq154 eq1362
    | (have j0 := eq1362 X0 X1 X2 X3
       grind)
    | (have r₁ := eq1362 X1 X2 X1 X3
       have r₂ := eq154 (M.op X1 X1) X1 X2
       grind)
    | exact resolve eq1362 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1362
  have eq1632 : ∀ X0 X1 X2 X3 : G, (k (M.op X0 X0) X3) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) (M.op X2 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1520 X0 X1 X2 X3
       grind)
    | (have r₁ := eq1520 X1 X1 X0 X3
       have r₂ := eq70 X0 X1
       grind)
    | (have r₁ := eq1520 X0 X1 X1 X3
       have r₂ := eq70 X0 X1
       grind)
    | exact resolve eq1520 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1520
  have eq1668 : ∀ X0 X2 X3 : G, (M.op X2 X2) = (k (M.op X0 X0) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1632 X0 x X2 X3
       have i₂ := eq154 (M.op X2 X2) X0 x
       grind)
    | exact superpose eq154 eq1632
    | exact resolve eq1632 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1632
  have eq1785 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (k (σ (M.op X1 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1)
       have i₂ := eq1668 X1 X0 (τ X2)
       grind)
    | exact superpose eq1668 eq16
    | exact resolve eq16 eq1668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1668
  have eq3026 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X4) X2) = (M.op (M.op X1 X2) (M.op (M.op X3 X3) (M.op (M.op X0 X0) X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op (M.op X4 X4) X2) (M.op X1 X2) X3
       have i₂ := eq213 X2 X4 X1 X0
       grind)
    | exact superpose eq213 eq8
    | exact resolve eq8 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3027 : ∀ X1 X2 X4 : G, (M.op (M.op X4 X4) X2) = (M.op (M.op X1 X2) X1) := by
    intro X1 X2 X4
    first
    | (have i₁ := eq3026 x X1 X2 x X4
       have i₂ := eq154 X1 x x
       grind)
    | exact superpose eq154 eq3026
    | exact resolve eq3026 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3026
  have eq3272 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X2)) X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 x
       have i₂ := eq3027 X0 (M.op X1 X2) x
       grind)
    | (have i₁ := eq8 X0 X1 (M.op X0 X1)
       have i₂ := eq3027 (M.op X0 X1) (M.op X0 X1) x
       grind)
    | exact superpose eq3027 eq8
    | exact resolve eq8 eq3027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3279 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X1) X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq154 X1 X2 x
       have i₂ := eq3027 X0 X1 x
       grind)
    | (have i₁ := eq154 X2 X1 X2
       have i₂ := eq3027 X2 X2 x
       grind)
    | exact superpose eq3027 eq154
    | exact resolve eq154 eq3027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3285 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X1) X2)) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X2 X2 X2 X1
       have i₂ := eq3027 X0 (M.op (M.op X1 X1) X2) (M.op X2 X2)
       grind)
    | (have i₁ := eq21 (M.op x x) (M.op x x) X2 x
       have i₂ := eq3027 (M.op (M.op x x) (M.op x x)) (M.op (M.op x x) X2) x
       grind)
    | exact superpose eq3027 eq21
    | exact resolve eq21 eq3027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq3483 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq468 X0
       have i₂ := eq48 X0 X0 X1
       grind)
    | exact superpose eq48 eq468
    | (have j0 := eq468 X0
       have j1 := eq48 X0 X1 X1
       grind)
    | exact resolve eq468 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq3508 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq468 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq468
    | (have j0 := eq468 (τ X0)
       grind)
    | exact resolve eq468 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq3522 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq3483 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3483
  have eq3523 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3508 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3508
    | (have j0 := eq3508 X0
       grind)
    | exact resolve eq3508 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3508
  have eq3532 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3523 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3523
    | (have j0 := eq3523 X0
       grind)
    | exact resolve eq3523 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3523
  have eq4089 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X0) X2) = (k (σ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (k X0 X1)
       have i₂ := eq124 X0 X1 X2
       grind)
    | exact superpose eq124 eq9
    | (have j1 := eq124 X0 X1 X2
       grind)
    | exact resolve eq9 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq4148 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) X2) = (k (σ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4089 X0 X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq4089
    | (have j0 := eq4089 X0 X1 X2
       grind)
    | exact resolve eq4089 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4089
  have eq4690 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq628 (σ (M.op X1 X1)) x
       have i₂ := eq1785 X0 X1 (τ (τ (τ (M.op x x))))
       grind)
    | exact superpose eq1785 eq628
    | exact resolve eq628 eq1785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628 eq1785
  have eq5573 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq428
       have i₂ := eq82 X0 x y
       grind)
    | exact superpose eq82 eq428
    | (have j1 := eq82 (σ x) (σ x) x
       grind)
    | exact resolve eq428 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq428
  have eq5574 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have j0 := eq5573 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5573
  have eq11071 : ∀ X0 X1 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq357 X0 (σ x)
       have i₂ := eq5574 X1
       grind)
    | exact superpose eq5574 eq357
    | (have j1 := eq5574 X1
       grind)
    | exact resolve eq357 eq5574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5574
  have eq11303 : ∀ X0 X1 : G, (k X0 x) = X0 ∨ x = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11071 X0 X1
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq11071
    | (have j0 := eq11071 X0 X1
       grind)
    | exact resolve eq11071 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11071
  have eq11647 : ∀ X1 X2 : G, x = (k x X1) ∨ (k X2 x) = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq157 X1 X1
       have i₂ := eq11303 x X1
       grind)
    | exact superpose eq11303 eq157
    | (have j1 := eq11303 X2 X1
       grind)
    | exact resolve eq157 eq11303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq11303
  have eq13228 : x ≠ x ∨ x = (k x x) := by
    first
    | (have j0 := eq11647 x x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11647
  have eq13229 : x = (k x x) := by grind
  clear eq13228
  have eq13558 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq13229
       grind)
    | exact superpose eq13229 eq12
    | (have j0 := eq12 x x
       grind)
    | exact resolve eq12 eq13229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13229
  have eq13563 : x = (M.op x x) := by grind
  clear eq13558
  have eq13971 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq70 X0 x
       have i₂ := eq13563
       grind)
    | exact superpose eq13563 eq70
    | exact resolve eq70 eq13563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq13977 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X0) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq154 X1 x X0
       have i₂ := eq13563
       grind)
    | exact superpose eq13563 eq154
    | exact resolve eq154 eq13563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq13987 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op x X2) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq213 X2 x X1 X0
       have i₂ := eq13563
       grind)
    | exact superpose eq13563 eq213
    | exact resolve eq213 eq13563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq13996 : ∀ X0 : G, (k X0 (τ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq357 X0 x
       have i₂ := eq13563
       grind)
    | exact superpose eq13563 eq357
    | exact resolve eq357 eq13563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq14004 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1050 X0 X1 x
       have i₂ := eq13563
       grind)
    | exact superpose eq13563 eq1050
    | exact resolve eq1050 eq13563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050
  have eq14010 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3027 X1 X0 x
       have i₂ := eq13563
       grind)
    | exact superpose eq13563 eq3027
    | exact resolve eq3027 eq13563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3027
  have eq14011 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X1) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3279 X0 X1 x
       have i₂ := eq13563
       grind)
    | exact superpose eq13563 eq3279
    | exact resolve eq3279 eq13563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3279
  have eq14012 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x X1)) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3285 X0 x X1
       have i₂ := eq13563
       grind)
    | exact superpose eq13563 eq3285
    | exact resolve eq3285 eq13563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3285
  have eq14016 : ∀ X0 : G, (σ x) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4690 X0 x
       have i₂ := eq13563
       grind)
    | exact superpose eq13563 eq4690
    | exact resolve eq4690 eq13563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13563
  have eq14051 : ∀ X1 X2 : G, (M.op x X1) = (M.op (M.op x X2) (M.op X1 X2)) := by
    intro X1 X2
    first
    | (have i₁ := eq13987 x X1 X2
       have i₂ := eq14004 X1 x
       grind)
    | exact superpose eq14004 eq13987
    | exact resolve eq13987 eq14004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13987
  have eq14058 : ∀ X1 : G, (M.op x (M.op x X1)) = X1 := by
    intro X1
    first
    | (have i₁ := eq13977 x X1
       have i₂ := eq14004 X1 x
       grind)
    | exact superpose eq14004 eq13977
    | exact resolve eq13977 eq14004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13977
  have eq15348 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ X1)) (M.op (M.op X2 X2) (σ (τ (k X0 X1))))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq448 (τ X0) (τ X1) X2
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq448
    | (have j0 := eq448 (τ X0) X1 X2
       grind)
    | exact resolve eq448 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15689 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X1)) (M.op x (σ (τ (k X0 X1))))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15348 X0 X1 x
       have i₂ := eq14004 (σ (τ (k X0 X1))) x
       grind)
    | exact superpose eq14004 eq15348
    | (have j0 := eq15348 X0 X1 x
       grind)
    | exact resolve eq15348 eq14004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15348
  have eq15871 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X1)) (M.op x (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15689 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq15689
    | (have j0 := eq15689 X0 X1
       grind)
    | exact resolve eq15689 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15689
  have eq15983 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 (M.op x (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15871 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq15871
    | (have j0 := eq15871 X0 X1
       grind)
    | exact resolve eq15871 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15871
  have eq16027 : ∀ X0 X1 : G, (M.op X1 (M.op x (k X0 X1))) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15983 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15983
    | (have j0 := eq15983 X0 X1
       grind)
    | exact resolve eq15983 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15983
  have eq16041 : ∀ X0 X1 : G, (σ (τ X0)) = x ∨ (M.op X1 (M.op x (k X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16027 X0 X1
       have i₂ := eq13971 (σ (τ X0))
       grind)
    | exact superpose eq13971 eq16027
    | (have j0 := eq16027 X0 X1
       grind)
    | exact resolve eq16027 eq13971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16027
  have eq16047 : ∀ X0 X1 : G, (M.op X1 (M.op x (k X0 X1))) = X0 ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16041 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16041
    | (have j0 := eq16041 X0 X1
       grind)
    | exact resolve eq16041 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16041
  have eq17959 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op X3 X3)) = (σ (M.op (M.op (M.op X0 X0) X1) (M.op X2 X1))) ∨ (M.op X2 X4) = (k X2 X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq4690 X3 (M.op X1 X1)
       have i₂ := eq242 X1 X0 X1 X2 X1 X4
       grind)
    | (have i₁ := eq4690 X0 (M.op (M.op X1 X1) X0)
       have i₂ := eq242 X0 X1 X0 (M.op X1 X1) X4 x
       grind)
    | exact superpose eq242 eq4690
    | (have j1 := eq242 X0 X1 X2 X2 X4 X4
       grind)
    | exact resolve eq4690 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242 eq4690
  have eq18415 : ∀ X1 X2 X3 X4 : G, (σ (M.op X3 X3)) = (σ (M.op (M.op x X1) (M.op X2 X1))) ∨ (M.op X2 X4) = (k X2 X4) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq17959 x X1 X2 X3 X4
       have i₂ := eq14004 X1 x
       grind)
    | exact superpose eq14004 eq17959
    | (have j0 := eq17959 x X1 X2 X3 X4
       grind)
    | exact resolve eq17959 eq14004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17959
  have eq18933 : ∀ X2 X3 X4 : G, (σ (M.op X3 X3)) = (σ (M.op x X2)) ∨ (M.op X2 X4) = (k X2 X4) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq18415 x X2 X3 X4
       have i₂ := eq14051 X2 x
       grind)
    | exact superpose eq14051 eq18415
    | (have j0 := eq18415 x X2 X3 X4
       grind)
    | exact resolve eq18415 eq14051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14051 eq18415
  have eq19323 : ∀ X2 X4 : G, (σ x) = (σ (M.op x X2)) ∨ (M.op X2 X4) = (k X2 X4) := by
    intro X2 X4
    first
    | (have i₁ := eq18933 X2 x X4
       have i₂ := eq14016 x
       grind)
    | exact superpose eq14016 eq18933
    | (have j0 := eq18933 X2 x X4
       grind)
    | exact resolve eq18933 eq14016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14016 eq18933
  have eq24299 : (τ x) ≠ (τ x) ∨ (τ x) = (M.op (τ x) (τ x)) := by
    first
    | (have i₁ := eq3532 (τ x)
       have i₂ := eq13996 (τ x)
       grind)
    | exact superpose eq13996 eq3532
    | (have j0 := eq3532 (τ x)
       grind)
    | (have r₁ := eq3532 (τ x)
       have r₂ := eq13996 (τ x)
       grind)
    | exact resolve eq3532 eq13996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3532 eq13996
  have eq24323 : (τ x) = (M.op (τ x) (τ x)) := by grind
  clear eq24299
  have eq24339 : x = (τ x) := by
    first
    | (have i₁ := eq24323
       have i₂ := eq13971 (τ x)
       grind)
    | exact superpose eq13971 eq24323
    | exact resolve eq24323 eq13971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24323
  have eq25279 : x = (σ x) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq24339
       grind)
    | exact superpose eq24339 eq10
    | exact resolve eq10 eq24339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24339
  have eq26313 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq25279
       grind)
    | exact superpose eq25279 eq14
    | exact resolve eq14 eq25279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53070 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X1)) X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq419 X0 (τ X1)
       grind)
    | exact superpose eq419 eq16
    | (have j1 := eq419 X0 (τ X1)
       grind)
    | exact resolve eq16 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq419
  have eq53202 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X1)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq53070 X0 X1
       have j1 := eq89 X0 (σ (τ X1)) X1
       grind)
    | (have r₁ := eq53070 X0 X1
       have r₂ := eq89 X0 (k (σ (τ X1)) X1) x
       grind)
    | (have r₁ := eq53070 X0 X1
       have r₂ := eq89 X0 (σ (τ X1)) x
       grind)
    | exact resolve eq53070 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq53070
  have eq53566 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53202 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq53202
    | exact resolve eq53202 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53202
  have eq53830 : ∀ X1 : G, x = (k X1 X1) := by
    intro X1
    first
    | (have i₁ := eq53566 x X1
       have i₂ := eq13971 x
       grind)
    | exact superpose eq13971 eq53566
    | exact resolve eq53566 eq13971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53566
  have eq54525 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq53830 X0
       have i₂ := eq633 X0 X0 X1
       grind)
    | exact superpose eq633 eq53830
    | (have j1 := eq633 X0 X1 X1
       grind)
    | exact resolve eq53830 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89172 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76 (σ X0) X1
       have i₂ := eq3522 X0 X2
       grind)
    | exact superpose eq3522 eq76
    | (have j1 := eq3522 X0 X2
       grind)
    | exact resolve eq76 eq3522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89205 : ∀ X0 X1 X2 : G, (σ X0) ≠ X1 ∨ (k X1 X1) = X1 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq289 (σ X0) X1
       have i₂ := eq3522 X0 X2
       grind)
    | exact superpose eq3522 eq289
    | (have j0 := eq289 X0 X1
       have j1 := eq3522 X0 X2
       grind)
    | (have r₁ := eq289 (σ X0) (σ X0)
       have r₂ := eq3522 X0 X1
       grind)
    | (have r₁ := eq289 X1 (k X1 X1)
       have r₂ := eq3522 X1 X1
       grind)
    | exact resolve eq289 eq3522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289 eq3522
  have eq89570 : ∀ X0 X1 X2 : G, (σ X0) ≠ X1 ∨ x = X1 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq89205 X0 X1 X2
       have i₂ := eq53830 X1
       grind)
    | exact superpose eq53830 eq89205
    | (have j0 := eq89205 X0 X1 X2
       grind)
    | exact resolve eq89205 eq53830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53830 eq89205
  have eq139160 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ X1) (M.op (M.op X2 X2) (σ (M.op (τ X0) X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ x = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq448 (τ X0) X1 X2
       have i₂ := eq54525 X0 X1
       grind)
    | exact superpose eq54525 eq448
    | (have j0 := eq448 (τ X0) X1 X2
       have j1 := eq54525 X0 X1
       grind)
    | exact resolve eq448 eq54525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448 eq54525
  have eq139258 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ X1) (M.op x (σ (M.op (τ X0) X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq139160 X0 X1 x
       have i₂ := eq14004 (σ (M.op (τ X0) X1)) x
       grind)
    | exact superpose eq14004 eq139160
    | (have j0 := eq139160 X0 X1 x
       grind)
    | exact resolve eq139160 eq14004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14004 eq139160
  have eq139342 : ∀ X0 X1 : G, (M.op (σ X1) (M.op x (σ (M.op (τ X0) X1)))) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq139258 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq139258
    | (have j0 := eq139258 X0 X1
       grind)
    | exact resolve eq139258 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139258
  have eq139401 : ∀ X0 X1 : G, (σ (τ X0)) = x ∨ (M.op (σ X1) (M.op x (σ (M.op (τ X0) X1)))) = X0 ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq139342 X0 X1
       have i₂ := eq13971 (σ (τ X0))
       grind)
    | exact superpose eq13971 eq139342
    | (have j0 := eq139342 X0 X1
       grind)
    | exact resolve eq139342 eq13971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13971 eq139342
  have eq139429 : ∀ X0 X1 : G, x = X0 ∨ (M.op (σ X1) (M.op x (σ (M.op (τ X0) X1)))) = X0 ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq139401 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq139401
    | (have j0 := eq139401 X0 X1
       grind)
    | exact resolve eq139401 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139401
  have eq139430 : ∀ X0 X1 : G, (M.op (σ X1) (M.op x (σ (M.op (τ X0) X1)))) = X0 ∨ x = X0 := by
    intro X0 X1
    first
    | (have j0 := eq139429 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139429
  have eq251736 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq89172 y (σ x) X0
       grind)
    | exact superpose eq89172 eq14
    | (have j1 := eq89172 y x X0
       grind)
    | exact resolve eq14 eq89172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89172
  have eq252183 : ∀ X0 : G, (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq251736 X0
       have j1 := eq19323 y X0
       grind)
    | (have r₁ := eq251736 X0
       have r₂ := eq19323 y x
       grind)
    | exact resolve eq251736 eq19323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19323 eq251736
  have eq254745 : ∀ X0 X1 : G, y = (M.op y X0) ∨ (k (τ y) X1) = (M.op (τ y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq633 y X0 X1
       have i₂ := eq252183 X0
       grind)
    | exact superpose eq252183 eq633
    | (have j0 := eq633 y X1 X1
       grind)
    | exact resolve eq633 eq252183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq254754 : ∀ X0 X1 : G, y = (M.op y X0) ∨ (k (σ y) X1) = (M.op (σ y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4148 y X0 X1
       have i₂ := eq252183 X0
       grind)
    | exact superpose eq252183 eq4148
    | (have j0 := eq4148 y X1 X1
       grind)
    | exact resolve eq4148 eq252183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4148
  have eq376889 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ x = X1 ∨ (M.op (τ X0) X2) = (k (τ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq89570 (τ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq89570
    | (have j0 := eq89570 (τ X0) X1 X2
       grind)
    | (have r₁ := eq89570 (τ X0) X0 X2
       have r₂ := eq10 X0
       grind)
    | (have r₁ := eq89570 X0 (σ (τ (σ X0))) X2
       have r₂ := eq10 (σ X0)
       grind)
    | exact resolve eq89570 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89570
  have eq443065 : ∀ X0 X1 X2 : G, (M.op X0 (M.op y y)) = X1 ∨ (k (τ y) X2) = (M.op (τ y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3272 y X1 X0
       have i₂ := eq254745 (M.op X1 X0) X2
       grind)
    | exact superpose eq254745 eq3272
    | (have j1 := eq254745 X0 X2
       grind)
    | exact resolve eq3272 eq254745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443107 : ∀ X0 X1 : G, y = X0 ∨ x = X0 ∨ (k (τ y) X1) = (M.op (τ y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16047 X0 y
       have i₂ := eq254745 (M.op x (k X0 y)) X1
       grind)
    | exact superpose eq254745 eq16047
    | (have j0 := eq16047 X0 X1
       have j1 := eq254745 X0 X1
       grind)
    | exact resolve eq16047 eq254745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16047 eq254745
  have eq443274 : ∀ X0 X1 : G, x = X0 ∨ (k (τ y) X1) = (M.op (τ y) X1) := by
    intro X0 X1
    first
    | (have j0 := eq443107 X0 X1
       have j1 := eq376889 y X0 X1
       grind)
    | (have r₁ := eq443107 X1 X1
       have r₂ := eq376889 y X1 x
       grind)
    | (have r₁ := eq443107 X0 X1
       have r₂ := eq376889 X0 y x
       grind)
    | (have r₁ := eq443107 X1 X1
       have r₂ := eq376889 x X1 x
       grind)
    | exact resolve eq443107 eq376889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376889 eq443107
  have eq443282 : ∀ X0 X1 X2 : G, X0 = X1 ∨ (k (τ y) X2) = (M.op (τ y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq443065 X0 X1 X2
       have i₂ := eq76 y X0
       grind)
    | exact superpose eq76 eq443065
    | (have j0 := eq443065 X0 X1 X2
       grind)
    | exact resolve eq443065 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443065
  have eq444035 : ∀ X0 : G, x ≠ (σ (M.op x y)) ∨ (k (τ y) X0) = (M.op (τ y) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq443274 (M.op (σ x) (σ y)) X0
       grind)
    | exact superpose eq443274 eq14
    | (have j1 := eq443274 X0 X0
       grind)
    | exact resolve eq14 eq443274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443274
  have eq444938 : ∀ X0 : G, (k (τ y) X0) = (M.op (τ y) X0) := by
    intro X0
    first
    | (have j0 := eq444035 X0
       have j1 := eq443282 (k (τ y) X0) (M.op (τ y) X0) X0
       grind)
    | (have r₁ := eq444035 X0
       have r₂ := eq443282 x (σ (M.op x y)) x
       grind)
    | (have r₁ := eq444035 X0
       have r₂ := eq443282 (σ (M.op x y)) x x
       grind)
    | exact resolve eq444035 eq443282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443282 eq444035
  have eq445304 : ∀ X0 : G, (τ (k y X0)) = (M.op (τ y) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 y
       have i₂ := eq444938 (τ X0)
       grind)
    | exact superpose eq444938 eq31
    | exact resolve eq31 eq444938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq444938
  have eq445592 : ∀ X0 : G, (τ (M.op y X0)) = (M.op (τ y) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq445304 X0
       have i₂ := eq252183 X0
       grind)
    | exact superpose eq252183 eq445304
    | exact resolve eq445304 eq252183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445304
  have eq446207 : ∀ X0 : G, (M.op x (τ X0)) = (M.op (τ (M.op y X0)) (τ y)) := by
    intro X0
    first
    | (have i₁ := eq14010 (τ X0) (τ y)
       have i₂ := eq445592 X0
       grind)
    | exact superpose eq445592 eq14010
    | exact resolve eq14010 eq445592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445592
  have eq462491 : ∀ X0 X1 X2 : G, (M.op X0 (M.op y y)) = X1 ∨ (M.op (σ y) X2) = (k (σ y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3272 y X1 X0
       have i₂ := eq254754 (M.op X1 X0) X2
       grind)
    | exact superpose eq254754 eq3272
    | (have j1 := eq254754 X0 X2
       grind)
    | exact resolve eq3272 eq254754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3272 eq254754
  have eq462649 : ∀ X0 X1 X2 : G, X0 = X1 ∨ (M.op (σ y) X2) = (k (σ y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq462491 X0 X1 X2
       have i₂ := eq76 y X0
       grind)
    | exact superpose eq76 eq462491
    | (have j0 := eq462491 X0 X1 X2
       grind)
    | exact resolve eq462491 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq462491
  have eq465253 : ∀ X0 X1 : G, (M.op (σ y) X0) ≠ X1 ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
    intro X0 X1
    first
    | (have j0 := eq462649 (M.op (σ y) X0) (k (σ y) X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq465256 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq465253 X0 x
       have j1 := eq462649 (M.op (σ y) X0) (k (σ y) X0) X0
       grind)
    | (have r₁ := eq465253 X0 x
       have r₂ := eq462649 (M.op (σ y) X0) x x
       grind)
    | (have r₁ := eq465253 X0 X0
       have r₂ := eq462649 X0 (M.op (σ y) X0) x
       grind)
    | (have r₁ := eq465253 x (k (σ y) x)
       have r₂ := eq462649 X0 x x
       grind)
    | exact resolve eq465253 eq462649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462649 eq465253
  have eq465686 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq465256 (σ X0)
       grind)
    | exact superpose eq465256 eq13
    | exact resolve eq13 eq465256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465256
  have eq465954 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq465686 X0
       have i₂ := eq252183 X0
       grind)
    | exact superpose eq252183 eq465686
    | exact resolve eq465686 eq252183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252183 eq465686
  have eq466646 : ∀ X0 : G, (M.op x (σ X0)) = (M.op (σ (M.op y X0)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14010 (σ X0) (σ y)
       have i₂ := eq465954 X0
       grind)
    | exact superpose eq465954 eq14010
    | exact resolve eq14010 eq465954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq466647 : ∀ X0 : G, (σ X0) = (M.op x (M.op (σ (M.op y X0)) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq14011 (σ y) (σ X0)
       have i₂ := eq465954 X0
       grind)
    | exact superpose eq465954 eq14011
    | exact resolve eq14011 eq465954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465954
  have eq800302 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14012 (σ X1) (σ (M.op (τ X0) X1))
       have i₂ := eq139430 X0 X1
       grind)
    | exact superpose eq139430 eq14012
    | (have j1 := eq139430 X0 X1
       grind)
    | exact resolve eq14012 eq139430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14012 eq139430
  have eq800399 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = x := by
    intro X0 X1
    first
    | (have i₁ := eq800302 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq800302
    | (have j0 := eq800302 (σ X0) X1
       grind)
    | exact resolve eq800302 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq800405 : ∀ X0 : G, (σ (M.op x (τ X0))) = (M.op (M.op y X0) (σ (τ y))) ∨ x = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq800302 (M.op y X0) (τ y)
       have i₂ := eq446207 X0
       grind)
    | exact superpose eq446207 eq800302
    | (have j0 := eq800302 (M.op y X0) x
       grind)
    | exact resolve eq800302 eq446207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446207 eq800302
  have eq800641 : ∀ X0 : G, (σ (M.op x (τ X0))) = (M.op (M.op y X0) y) ∨ x = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq800405 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq800405
    | (have j0 := eq800405 X0
       grind)
    | exact resolve eq800405 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800405
  have eq800686 : ∀ X0 : G, (M.op x X0) = (σ (M.op x (τ X0))) ∨ x = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq800641 X0
       have i₂ := eq14010 X0 y
       grind)
    | exact superpose eq14010 eq800641
    | (have j0 := eq800641 X0
       grind)
    | exact resolve eq800641 eq14010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800641
  have eq801842 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op (M.op y X0) y)) ∨ x = (σ (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq466646 X0
       have i₂ := eq800399 (M.op y X0) y
       grind)
    | exact superpose eq800399 eq466646
    | (have j1 := eq800399 (M.op y X0) x
       grind)
    | exact resolve eq466646 eq800399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466646 eq800399
  have eq802110 : ∀ X0 : G, x = (σ (M.op y X0)) ∨ (M.op x (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq801842 X0
       have i₂ := eq14010 X0 y
       grind)
    | exact superpose eq14010 eq801842
    | (have j0 := eq801842 X0
       grind)
    | exact resolve eq801842 eq14010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801842
  have eq802765 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) ∨ x = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq800686 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq800686
    | (have j0 := eq800686 (σ X0)
       grind)
    | exact resolve eq800686 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800686
  have eq966416 : (M.op x (σ y)) ≠ (M.op x (σ y)) ∨ x = (M.op y (σ y)) := by
    first
    | (have i₁ := eq26313
       have i₂ := eq802765 y
       grind)
    | exact superpose eq802765 eq26313
    | (have j1 := eq802765 y
       grind)
    | (have r₁ := eq26313
       have r₂ := eq802765 y
       grind)
    | exact resolve eq26313 eq802765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26313 eq802765
  have eq966427 : x = (M.op y (σ y)) := by grind
  clear eq966416
  have eq966695 : (M.op x y) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq14010 (σ y) y
       have i₂ := eq966427
       grind)
    | exact superpose eq966427 eq14010
    | exact resolve eq14010 eq966427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14010
  have eq966696 : (σ y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq14011 y (σ y)
       have i₂ := eq966427
       grind)
    | exact superpose eq966427 eq14011
    | exact resolve eq14011 eq966427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14011 eq966427
  have eq966920 : y = (σ y) := by
    first
    | (have i₁ := eq966696
       have i₂ := eq14058 y
       grind)
    | (have i₁ := eq966696
       have i₂ := eq14058 (M.op x (M.op x y))
       grind)
    | exact superpose eq14058 eq966696
    | exact resolve eq966696 eq14058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966696
  have eq967518 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq966920
       grind)
    | exact superpose eq966920 eq14
    | exact resolve eq14 eq966920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq967558 : ∀ X0 : G, (σ X0) = (M.op x (M.op (σ (M.op y X0)) y)) := by
    intro X0
    first
    | (have i₁ := eq466647 X0
       have i₂ := eq966920
       grind)
    | exact superpose eq966920 eq466647
    | exact resolve eq466647 eq966920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466647
  have eq968169 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq967518
       have i₂ := eq25279
       grind)
    | exact superpose eq25279 eq967518
    | exact resolve eq967518 eq25279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25279 eq967518
  have eq980870 : ∀ X0 : G, (σ X0) = (M.op x (M.op x y)) ∨ (M.op x (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq967558 X0
       have i₂ := eq802110 X0
       grind)
    | exact superpose eq802110 eq967558
    | (have j1 := eq802110 X0
       grind)
    | exact resolve eq967558 eq802110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802110 eq967558
  have eq981196 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) ∨ (σ X0) = y := by
    intro X0
    first
    | (have i₁ := eq980870 X0
       have i₂ := eq14058 y
       grind)
    | (have i₁ := eq980870 X0
       have i₂ := eq14058 (M.op x (M.op x y))
       grind)
    | exact superpose eq14058 eq980870
    | (have j0 := eq980870 X0
       grind)
    | exact resolve eq980870 eq14058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980870
  have eq1000785 : ∀ X0 : G, (M.op x X0) = (τ (M.op x (σ X0))) ∨ (σ X0) = y := by
    intro X0
    first
    | (have i₁ := eq9 (M.op x X0)
       have i₂ := eq981196 X0
       grind)
    | exact superpose eq981196 eq9
    | (have j1 := eq981196 X0
       grind)
    | exact resolve eq9 eq981196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981196
  have eq1002062 : ∀ X0 : G, (M.op x (τ X0)) = (τ (M.op x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq1000785 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1000785
    | exact resolve eq1000785 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000785
  have eq1002162 : ∀ X0 : G, (τ X0) = (M.op x (τ (M.op x X0))) ∨ y = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq1002062 (M.op x X0)
       have i₂ := eq14058 X0
       grind)
    | exact superpose eq14058 eq1002062
    | (have j0 := eq1002062 (M.op x X0)
       grind)
    | exact resolve eq1002062 eq14058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002062
  have eq1025721 : (τ (σ y)) = (M.op x (τ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1002162 (σ y)
       have i₂ := eq966695
       grind)
    | exact superpose eq966695 eq1002162
    | (have j0 := eq1002162 y
       grind)
    | exact resolve eq1002162 eq966695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966695 eq1002162
  have eq1025779 : y = (M.op x (τ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1025721
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1025721
    | exact resolve eq1025721 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025721
  have eq1025825 : (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14058 (τ (M.op x y))
       have i₂ := eq1025779
       grind)
    | exact superpose eq1025779 eq14058
    | exact resolve eq14058 eq1025779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14058 eq1025779
  have eq1025891 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq1025825
       grind)
    | exact superpose eq1025825 eq10
    | exact resolve eq10 eq1025825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025825
  have eq1025895 : y = (M.op x y) := by
    first
    | (have r₁ := eq1025891
       have r₂ := eq968169
       grind)
    | exact resolve eq1025891 eq968169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025891
  have eq1025983 : y ≠ (σ y) := by
    first
    | (have i₁ := eq968169
       have i₂ := eq1025895
       grind)
    | exact superpose eq1025895 eq968169
    | exact resolve eq968169 eq1025895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968169 eq1025895
  have eq1026532 : False := by grind
  exact eq1026532

/-- `Equation978`: `x = y ◇ ((z ◇ z) ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_pyx_pxy_Equation978 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law978 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law978.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X2) (M.op X0 X1))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) (M.op (M.op X3 X3) X0)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op (M.op X1 X1) (M.op X0 X2)) X3
       have i₂ := eq8 X0 X2 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op X1 X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X2 X2) (M.op X0 (M.op X1 X1)) X1
       have i₂ := eq8 X0 (M.op X1 X1) X2
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
  have eq40 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X2) = (k X0 X2) := by
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
  have eq41 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X2 X1))) = X2 ∨ (M.op X0 X3) = (k X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X1 X0
       have i₂ := eq12 X0 X3
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X3
       grind)
    | exact resolve eq8 eq12
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
  have eq46 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
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
  have eq48 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq40 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq70 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 x x X0
       have i₂ := eq22 x x X1
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) X0) = X2 ∨ (M.op X2 X3) = (k X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X2 X3
       have i₂ := eq22 X0 X1 X2
       grind)
    | exact superpose eq22 eq12
    | (have j0 := eq12 X2 X3
       grind)
    | exact resolve eq12 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X1 (M.op X1 X1)
       have i₂ := eq22 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq82 : ∀ X0 X2 X3 : G, (M.op X0 X0) = X2 ∨ (M.op X2 X3) = (k X2 X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq71 X0 x X2 X3
       have i₂ := eq76 x X0
       grind)
    | exact superpose eq76 eq71
    | (have j0 := eq71 X0 x X2 X3
       grind)
    | exact resolve eq71 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq134 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq147 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k (M.op X0 X0) X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0) X1
       have i₂ := eq76 X0 (M.op X0 X0)
       grind)
    | exact superpose eq76 eq11
    | (have j0 := eq11 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq11 (M.op X0 X0) X1
       have r₂ := eq76 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X2) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 (M.op X1 X1) X2
       have i₂ := eq76 X1 X0
       grind)
    | exact superpose eq76 eq8
    | exact resolve eq8 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq147 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq157 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq155 X0 X1
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq155
    | exact resolve eq155 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq155
  have eq170 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X2 X2) X0)) = X0 ∨ (M.op X0 X3) = (k X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X0 X1 X0 X2
       have i₂ := eq12 X0 X3
       grind)
    | exact superpose eq12 eq21
    | (have j1 := eq12 X0 X3
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X4) X3) = (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X5 X5) (M.op (M.op X2 X2) (M.op X3 X0)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq21 (M.op (M.op X2 X2) (M.op X3 X0)) X1 (M.op (M.op X4 X4) X3) X5
       have i₂ := eq21 X3 X2 X0 X4
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X4) (M.op X2 X0)) = (M.op (M.op (M.op X1 X1) X2) (M.op (M.op X3 X3) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op (M.op X4 X4) (M.op X2 X0)) (M.op (M.op X1 X1) X2) X3
       have i₂ := eq21 X2 X4 X0 X1
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X4 X4) X3) = (M.op (M.op (M.op X1 X1) X0) (M.op X3 X0)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq172 X0 X1 x X3 X4 x
       have i₂ := eq152 (M.op X3 X0) x x
       grind)
    | exact superpose eq152 eq172
    | exact resolve eq172 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq225 : ∀ X0 X1 X2 : G, (k X0 X1) = X1 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq157 X0 X1
       have i₂ := eq12 X0 X2
       grind)
    | exact superpose eq12 eq157
    | (have j1 := eq12 X0 X2
       grind)
    | exact resolve eq157 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X1 X1)
       have i₂ := eq157 X1 (τ X0)
       grind)
    | exact superpose eq157 eq16
    | exact resolve eq16 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq236 : ∀ X0 X1 : G, (k (σ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq229 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq229
    | exact resolve eq229 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq255 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op X3 X3) ∨ (M.op (M.op (M.op X2 X2) (M.op X1 X0)) X4) = (k (M.op (M.op X2 X2) (M.op X1 X0)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq41 (M.op (M.op X2 X2) (M.op X1 X0)) X1 (M.op X3 X3) X4
       have i₂ := eq21 X1 X2 X0 X3
       grind)
    | exact superpose eq21 eq41
    | (have j0 := eq41 (M.op (M.op X2 X2) (M.op X1 X0)) X1 X2 X4
       grind)
    | exact resolve eq41 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq367 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (σ (M.op X1 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (σ (M.op X1 X1))
       have i₂ := eq236 (τ X0) X1
       grind)
    | exact superpose eq236 eq16
    | exact resolve eq16 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 X1 : G, (k (σ (σ (M.op X1 X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq367 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq367
    | exact resolve eq367 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq445 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq465 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X1) (M.op (M.op X2 X2) (σ (k X0 X1)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (σ X0) (σ X1) X2
       have i₂ := eq44 X0 X1
       grind)
    | exact superpose eq44 eq8
    | (have j1 := eq44 X0 X1
       grind)
    | exact resolve eq8 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq485 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq44 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq671 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq134 X0 X0
       have i₂ := eq70 X0 X1
       grind)
    | (have i₁ := eq134 X1 X1
       have i₂ := eq70 X0 X1
       grind)
    | exact superpose eq70 eq134
    | (have j0 := eq134 X0 X0
       grind)
    | (have r₁ := eq134 X1 X1
       have r₂ := eq70 X1 X1
       grind)
    | (have r₁ := eq134 X0 X0
       have r₂ := eq70 X0 X0
       grind)
    | exact resolve eq134 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq678 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq134 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq682 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq671 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq714 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq678 (σ X0)
       grind)
    | exact superpose eq678 eq13
    | exact resolve eq13 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq726 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq714 X0
       have i₂ := eq678 X0
       grind)
    | exact superpose eq678 eq714
    | exact resolve eq714 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678 eq714
  have eq840 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq135 X0 X0
       have i₂ := eq682 X0 X1
       grind)
    | exact superpose eq682 eq135
    | exact resolve eq135 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq860 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq236 (σ (M.op X1 X1)) X1
       have i₂ := eq682 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq682 eq236
    | exact resolve eq236 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq861 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq376 (σ (σ (M.op X1 X1))) X1
       have i₂ := eq682 X0 (σ (σ (M.op X1 X1)))
       grind)
    | exact superpose eq682 eq376
    | exact resolve eq376 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq863 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X1)
       have i₂ := eq682 X0 (τ X1)
       grind)
    | exact superpose eq682 eq15
    | exact resolve eq15 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq867 : ∀ X0 X1 : G, (k X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq840 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq871 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq863 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq863
    | exact resolve eq863 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq1049 : ∀ X0 X1 : G, (k X0 X0) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq376 (σ (σ (M.op X1 X1))) X1
       have i₂ := eq867 (σ (σ (M.op X1 X1))) X0
       grind)
    | (have i₁ := eq376 (σ (σ (M.op X1 X1))) X1
       have i₂ := eq867 X0 (σ (σ (M.op X1 X1)))
       grind)
    | exact superpose eq867 eq376
    | exact resolve eq376 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq1212 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq236 (σ (M.op X0 X0)) X0
       have i₂ := eq871 X1 (σ (M.op X0 X0))
       grind)
    | exact superpose eq871 eq236
    | exact resolve eq236 eq871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1213 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq376 (σ (σ (M.op X1 X1))) X1
       have i₂ := eq871 X0 (σ (σ (M.op X1 X1)))
       grind)
    | exact superpose eq871 eq376
    | exact resolve eq376 eq871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376 eq871
  have eq1574 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X1 X1
       have i₂ := eq860 (M.op X1 X1) X0
       grind)
    | exact superpose eq860 eq8
    | exact resolve eq8 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1631 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq46 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq46
    | (have j0 := eq46 X1 X1
       grind)
    | exact resolve eq46 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq1745 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1631 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1631
    | (have j0 := eq1631 X0 X1
       grind)
    | exact resolve eq1631 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1631
  have eq2345 : ∀ X0 X1 X3 : G, (M.op X1 (σ X0)) = X1 ∨ (M.op X0 X3) = (k X0 X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1574 x X1
       have i₂ := eq82 x X0 X3
       grind)
    | (have i₁ := eq1574 X0 X1
       have i₂ := eq82 X0 (M.op X0 X0) X3
       grind)
    | exact superpose eq82 eq1574
    | (have j1 := eq82 X0 X0 X3
       grind)
    | exact resolve eq1574 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2349 : ∀ X0 X1 : G, (M.op X1 (σ (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1574 (σ (M.op X0 X0)) X1
       have i₂ := eq1574 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq1574 eq1574
    | exact resolve eq1574 eq1574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1574
  have eq2975 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X4) X2) = (M.op (M.op X1 X2) (M.op (M.op X3 X3) (M.op (M.op X0 X0) X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op (M.op X4 X4) X2) (M.op X1 X2) X3
       have i₂ := eq212 X2 X4 X1 X0
       grind)
    | exact superpose eq212 eq8
    | exact resolve eq8 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq2983 : ∀ X1 X2 X4 : G, (M.op (M.op X4 X4) X2) = (M.op (M.op X1 X2) X1) := by
    intro X1 X2 X4
    first
    | (have i₁ := eq2975 x X1 X2 x X4
       have i₂ := eq152 X1 x x
       grind)
    | exact superpose eq152 eq2975
    | exact resolve eq2975 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq2975
  have eq4214 : ∀ X0 X2 : G, (σ (M.op X2 X2)) = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq1212 X2 x
       have i₂ := eq861 x X0
       grind)
    | exact superpose eq861 eq1212
    | exact resolve eq1212 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861
  have eq4861 : ∀ X0 X1 : G, (σ X1) ≠ (σ (σ (σ (M.op X0 X0)))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq485 X1
       have i₂ := eq1049 X1 X0
       grind)
    | exact superpose eq1049 eq485
    | (have j0 := eq485 X1
       grind)
    | exact resolve eq485 eq1049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485 eq1049
  have eq4937 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (σ X1) ≠ (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4861 X0 X1
       have i₂ := eq726 X1
       grind)
    | exact superpose eq726 eq4861
    | (have j0 := eq4861 X0 X1
       grind)
    | exact resolve eq4861 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4861
  have eq5340 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq445
       have i₂ := eq82 X0 x y
       grind)
    | exact superpose eq82 eq445
    | (have j1 := eq82 (σ x) (σ x) x
       grind)
    | exact resolve eq445 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq5341 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have j0 := eq5340 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5340
  have eq5344 : ∀ X0 : G, (σ x) = (σ (M.op x x)) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq5341 X0
       have i₂ := eq726 x
       grind)
    | exact superpose eq726 eq5341
    | (have j0 := eq5341 X0
       grind)
    | exact resolve eq5341 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5341
  have eq5353 : ∀ X0 X1 X3 : G, (M.op X1 (σ (σ X0))) = X1 ∨ (M.op X0 X3) = (k X0 X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq2349 x X1
       have i₂ := eq82 x X0 X3
       grind)
    | (have i₁ := eq2349 X0 X1
       have i₂ := eq82 X0 (M.op X0 X0) X3
       grind)
    | exact superpose eq82 eq2349
    | (have j1 := eq82 X0 X0 X3
       grind)
    | exact resolve eq2349 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq2349
  have eq8124 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X2) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X1 x X2 x
       have i₂ := eq200 X1 x (M.op X1 X2) x X0
       grind)
    | (have i₁ := eq21 X0 X0 X0 x
       have i₂ := eq200 X0 X1 (M.op x x) x (M.op X0 X0)
       grind)
    | exact superpose eq200 eq21
    | exact resolve eq21 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq17590 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (M.op X2 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2983 X2 X1 (σ X0)
       have i₂ := eq726 X0
       grind)
    | exact superpose eq726 eq2983
    | exact resolve eq2983 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17594 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X3 X1) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq2983 X3 X1 x
       have i₂ := eq2983 X0 X1 x
       grind)
    | (have i₁ := eq2983 X1 x x
       have i₂ := eq2983 x x x
       grind)
    | exact superpose eq2983 eq2983
    | exact resolve eq2983 eq2983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17763 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X2)) X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 x
       have i₂ := eq2983 X0 (M.op X1 X2) x
       grind)
    | (have i₁ := eq8 X0 X1 (M.op X0 X1)
       have i₂ := eq2983 (M.op X0 X1) (M.op X0 X1) x
       grind)
    | exact superpose eq2983 eq8
    | exact resolve eq8 eq2983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18674 : ∀ X0 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X2 X0) X2)) X3) = X0 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq2983 X3 (M.op (M.op X2 X0) X2) x
       have i₂ := eq8124 x X2 X0
       grind)
    | exact superpose eq8124 eq2983
    | exact resolve eq2983 eq8124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2983 eq8124
  have eq20997 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (τ X1)) (M.op (M.op X2 X2) (k (σ X0) X1))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq465 X0 (τ X1) X2
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq465
    | (have j0 := eq465 X0 X1 X2
       grind)
    | exact resolve eq465 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq21291 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (M.op (M.op X2 X2) (k (σ X0) X1))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20997 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq20997
    | (have j0 := eq20997 X0 X1 X2
       grind)
    | exact resolve eq20997 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20997
  have eq21414 : ∀ X0 X1 X2 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (M.op (M.op X2 X2) (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21291 X0 X1 X2
       have i₂ := eq726 X0
       grind)
    | exact superpose eq726 eq21291
    | (have j0 := eq21291 X0 X1 X2
       grind)
    | exact resolve eq21291 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726 eq21291
  have eq44493 : ∀ X1 : G, (σ x) = (σ (σ (σ (M.op X1 X1)))) ∨ (σ x) = (σ (M.op x x)) := by
    intro X1
    first
    | (have i₁ := eq4214 X1 x
       have i₂ := eq5344 x
       grind)
    | exact superpose eq5344 eq4214
    | exact resolve eq4214 eq5344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4214 eq5344
  have eq44706 : (σ x) = (σ (M.op x x)) := by
    first
    | (have j1 := eq4937 x x
       grind)
    | (have r₁ := eq44493 x
       have r₂ := eq4937 x x
       grind)
    | exact resolve eq44493 eq4937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4937 eq44493
  have eq45839 : ∀ X0 : G, (k (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq236 X0 x
       have i₂ := eq44706
       grind)
    | exact superpose eq44706 eq236
    | exact resolve eq236 eq44706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq45842 : ∀ X0 : G, (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq860 X0 x
       have i₂ := eq44706
       grind)
    | exact superpose eq44706 eq860
    | exact resolve eq860 eq44706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860
  have eq45847 : ∀ X0 : G, (σ x) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1212 x X0
       have i₂ := eq44706
       grind)
    | exact superpose eq44706 eq1212
    | exact resolve eq1212 eq44706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq45848 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1213 X0 x
       have i₂ := eq44706
       grind)
    | exact superpose eq44706 eq1213
    | exact resolve eq1213 eq44706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213
  have eq45863 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq44706
       grind)
    | exact superpose eq44706 eq9
    | exact resolve eq9 eq44706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44706
  have eq45941 : x = (M.op x x) := by
    first
    | (have i₁ := eq45863
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq45863
    | exact resolve eq45863 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45863
  have eq45969 : x = (σ x) := by
    first
    | (have i₁ := eq45941
       have i₂ := eq45842 x
       grind)
    | exact superpose eq45842 eq45941
    | exact resolve eq45941 eq45842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45941
  have eq46777 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq45969
       grind)
    | exact superpose eq45969 eq14
    | exact resolve eq14 eq45969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49456 : ∀ X0 : G, (k x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq45839 X0
       have i₂ := eq45969
       grind)
    | exact superpose eq45969 eq45839
    | exact resolve eq45839 eq45969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45839
  have eq52427 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq682 X0 x
       have i₂ := eq49456 x
       grind)
    | exact superpose eq49456 eq682
    | exact resolve eq682 eq49456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682 eq49456
  have eq55522 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17594 X0 X1 X1
       have i₂ := eq52427 X1
       grind)
    | exact superpose eq52427 eq17594
    | exact resolve eq17594 eq52427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17594
  have eq55524 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x X1)) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18674 X1 X1 X0
       have i₂ := eq52427 X1
       grind)
    | exact superpose eq52427 eq18674
    | exact resolve eq18674 eq52427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55537 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X1) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18674 X1 X0 (M.op (M.op X0 X1) X0)
       have i₂ := eq52427 (M.op (M.op X0 X1) X0)
       grind)
    | exact superpose eq52427 eq18674
    | exact resolve eq18674 eq52427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55555 : ∀ X0 X1 : G, (M.op x (M.op (M.op X1 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0 X0 X0 X1
       have i₂ := eq52427 (M.op X0 X0)
       grind)
    | exact superpose eq52427 eq21
    | exact resolve eq21 eq52427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq55688 : ∀ X0 : G, (M.op x (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq55555 X0 x
       have i₂ := eq45842 x
       grind)
    | exact superpose eq45842 eq55555
    | exact resolve eq55555 eq45842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55555
  have eq55904 : ∀ X0 : G, (M.op x (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq55688 X0
       have i₂ := eq45969
       grind)
    | exact superpose eq45969 eq55688
    | exact resolve eq55688 eq45969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55688
  have eq60633 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq52427 X0
       have i₂ := eq1745 X1 X0
       grind)
    | exact superpose eq1745 eq52427
    | (have j1 := eq1745 X1 X0
       grind)
    | exact resolve eq52427 eq1745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1745 eq52427
  have eq128440 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) ≠ (M.op x (σ y)) ∨ (M.op (M.op (M.op X1 X1) (M.op x y)) X2) = (k (M.op (M.op X1 X1) (M.op x y)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46777
       have i₂ := eq255 y x X1 X0 X2
       grind)
    | exact superpose eq255 eq46777
    | (have j1 := eq255 y x X1 x X2
       grind)
    | exact resolve eq46777 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq128441 : ∀ X1 X2 : G, (σ (σ x)) ≠ (M.op x (σ y)) ∨ (M.op (M.op (M.op X1 X1) (M.op x y)) X2) = (k (M.op (M.op X1 X1) (M.op x y)) X2) := by
    intro X1 X2
    first
    | (have i₁ := eq128440 x X1 X2
       have i₂ := eq45848 x
       grind)
    | exact superpose eq45848 eq128440
    | (have j0 := eq128440 x X1 X2
       grind)
    | exact resolve eq128440 eq45848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45848 eq128440
  have eq128442 : ∀ X1 X2 : G, (σ x) ≠ (M.op x (σ y)) ∨ (M.op (M.op (M.op X1 X1) (M.op x y)) X2) = (k (M.op (M.op X1 X1) (M.op x y)) X2) := by
    intro X1 X2
    first
    | (have i₁ := eq128441 X1 X2
       have i₂ := eq45969
       grind)
    | exact superpose eq45969 eq128441
    | (have j0 := eq128441 X1 X2
       grind)
    | exact resolve eq128441 eq45969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128441
  have eq128443 : ∀ X1 X2 : G, x ≠ (M.op x (σ y)) ∨ (M.op (M.op (M.op X1 X1) (M.op x y)) X2) = (k (M.op (M.op X1 X1) (M.op x y)) X2) := by
    intro X1 X2
    first
    | (have i₁ := eq128442 X1 X2
       have i₂ := eq45969
       grind)
    | exact superpose eq45969 eq128442
    | (have j0 := eq128442 X1 X2
       grind)
    | exact resolve eq128442 eq45969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128442
  have eq128444 : ∀ X2 : G, (M.op (M.op (σ x) (M.op x y)) X2) = (k (M.op (σ x) (M.op x y)) X2) ∨ x ≠ (M.op x (σ y)) := by
    intro X2
    first
    | (have i₁ := eq128443 x X2
       have i₂ := eq45842 x
       grind)
    | exact superpose eq45842 eq128443
    | exact resolve eq128443 eq45842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128443
  have eq128445 : ∀ X2 : G, (M.op (M.op x (M.op x y)) X2) = (k (M.op x (M.op x y)) X2) ∨ x ≠ (M.op x (σ y)) := by
    intro X2
    first
    | (have i₁ := eq128444 X2
       have i₂ := eq45969
       grind)
    | exact superpose eq45969 eq128444
    | exact resolve eq128444 eq45969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128444
  have eq128446 : ∀ X2 : G, (M.op y X2) = (k y X2) ∨ x ≠ (M.op x (σ y)) := by
    intro X2
    first
    | (have i₁ := eq128445 X2
       have i₂ := eq55904 y
       grind)
    | exact superpose eq55904 eq128445
    | exact resolve eq128445 eq55904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128445
  have eq128447 : ∀ X2 : G, (M.op y X2) = (k y X2) := by
    intro X2
    first
    | (have j0 := eq128446 X2
       have j1 := eq2345 y x X2
       grind)
    | (have r₁ := eq128446 X2
       have r₂ := eq2345 y x x
       grind)
    | exact resolve eq128446 eq2345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2345 eq128446
  have eq131406 : ∀ X0 : G, (k (τ y) X0) = (τ (M.op y (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq20 y X0
       have i₂ := eq128447 (σ X0)
       grind)
    | exact superpose eq128447 eq20
    | exact resolve eq20 eq128447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq200420 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq225 X0 X1 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq202116 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k (M.op X1 (M.op x X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq200420 (M.op X1 (M.op x X0)) X1
       have i₂ := eq55524 X1 X0
       grind)
    | exact superpose eq55524 eq200420
    | (have j0 := eq200420 (M.op X1 (M.op x X0)) X1
       grind)
    | (have r₁ := eq200420 (M.op X1 (M.op x X1)) X1
       have r₂ := eq55524 X1 X1
       grind)
    | exact resolve eq200420 eq55524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200420
  have eq244481 : ∀ X0 X2 X3 X4 : G, (M.op (σ X0) X2) = (M.op (M.op X3 X2) X3) ∨ (M.op X0 X4) = (k X0 X4) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq17590 (M.op (M.op x x) X0) X2 X3
       have i₂ := eq170 X0 x x X4
       grind)
    | exact superpose eq170 eq17590
    | (have j1 := eq170 X0 x X2 X4
       grind)
    | exact resolve eq17590 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170 eq17590
  have eq246535 : ∀ X0 X2 X4 : G, (M.op (σ X0) X2) = (M.op x X2) ∨ (M.op X0 X4) = (k X0 X4) := by
    intro X0 X2 X4
    first
    | (have i₁ := eq244481 X0 X2 x X4
       have i₂ := eq55522 x X2
       grind)
    | exact superpose eq55522 eq244481
    | (have j0 := eq244481 X0 X2 x X4
       grind)
    | exact resolve eq244481 eq55522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244481
  have eq415416 : ∀ X0 : G, (k (M.op X0 (M.op x X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq202116 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202116
  have eq416399 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (M.op x (τ X0)))) X0) := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op (τ X0) (M.op x (τ X0)))
       have i₂ := eq415416 (τ X0)
       grind)
    | exact superpose eq415416 eq16
    | exact resolve eq16 eq415416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq415416
  have eq416407 : ∀ X0 : G, (k (σ (M.op (τ X0) (M.op x (τ X0)))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq416399 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq416399
    | exact resolve eq416399 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416399
  have eq530497 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ X0) = (M.op X1 (M.op (M.op X2 X2) (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0)
       have i₂ := eq21414 X0 X1 X2
       grind)
    | exact superpose eq21414 eq9
    | (have j1 := eq21414 X0 X1 X2
       grind)
    | exact resolve eq9 eq21414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21414
  have eq530541 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (σ x) ∨ (σ X0) = (M.op X1 (M.op (M.op X2 X2) (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq530497 X0 X1 X2
       have i₂ := eq45842 X0
       grind)
    | exact superpose eq45842 eq530497
    | (have j0 := eq530497 X0 X1 X2
       grind)
    | exact resolve eq530497 eq45842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530497
  have eq530635 : ∀ X0 X1 X2 : G, (τ (σ X0)) = x ∨ (σ X0) = (M.op X1 (M.op (M.op X2 X2) (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq530541 X0 X1 X2
       have i₂ := eq45969
       grind)
    | exact superpose eq45969 eq530541
    | (have j0 := eq530541 X0 X1 X2
       grind)
    | exact resolve eq530541 eq45969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530541
  have eq530716 : ∀ X0 X1 X2 : G, x = X0 ∨ (σ X0) = (M.op X1 (M.op (M.op X2 X2) (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq530635 X0 X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq530635
    | (have j0 := eq530635 X0 X1 X2
       grind)
    | exact resolve eq530635 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530635
  have eq530786 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op (σ x) (k (σ X0) X1))) ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq530716 X0 X1 x
       have i₂ := eq45842 x
       grind)
    | exact superpose eq45842 eq530716
    | (have j0 := eq530716 X0 X1 x
       grind)
    | exact resolve eq530716 eq45842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45842 eq530716
  have eq530848 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op x (k (σ X0) X1))) ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq530786 X0 X1
       have i₂ := eq45969
       grind)
    | exact superpose eq45969 eq530786
    | (have j0 := eq530786 X0 X1
       grind)
    | exact resolve eq530786 eq45969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530786
  have eq601790 : ∀ X0 X1 : G, (M.op X1 (M.op x (k X0 X1))) = X0 ∨ (τ X0) = x := by
    intro X0 X1
    first
    | (have i₁ := eq530848 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq530848
    | (have j0 := eq530848 (τ X0) X1
       grind)
    | exact resolve eq530848 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530848
  have eq602713 : ∀ X0 X1 : G, x = (M.op (k X0 X1) (M.op X0 X1)) ∨ (τ X0) = x := by
    intro X0 X1
    first
    | (have i₁ := eq17763 X1 x (k X0 X1)
       have i₂ := eq601790 X0 X1
       grind)
    | exact superpose eq601790 eq17763
    | (have j1 := eq601790 X0 X1
       grind)
    | exact resolve eq17763 eq601790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17763 eq601790
  have eq603651 : ∀ X0 X1 : G, x = (M.op (σ (k X0 X1)) (M.op (σ X0) (σ X1))) ∨ (τ (σ X0)) = x := by
    intro X0 X1
    first
    | (have i₁ := eq602713 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq602713
    | (have j0 := eq602713 (σ X0) X1
       grind)
    | exact resolve eq602713 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq603847 : ∀ X0 X1 : G, (M.op x (k (M.op X0 X1) X0)) = X1 ∨ x = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18674 X1 X0 (k (M.op X0 X1) X0)
       have i₂ := eq602713 (M.op X0 X1) X0
       grind)
    | exact superpose eq602713 eq18674
    | (have j1 := eq602713 (M.op X0 X1) X1
       grind)
    | exact resolve eq18674 eq602713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18674 eq602713
  have eq604043 : ∀ X0 X1 : G, x = (M.op (σ (k X0 X1)) (M.op (σ X0) (σ X1))) ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq603651 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq603651
    | (have j0 := eq603651 X0 X1
       grind)
    | exact resolve eq603651 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603651
  have eq687167 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (k (τ X0) X2) = (M.op (τ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5353 (τ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5353
    | (have j0 := eq5353 (τ X0) X1 X2
       grind)
    | exact resolve eq5353 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5353
  have eq971439 : ∀ X0 X1 : G, (σ x) = (σ (M.op x (σ X0))) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45847 (σ X0)
       have i₂ := eq246535 X0 (σ X0) X1
       grind)
    | exact superpose eq246535 eq45847
    | (have j1 := eq246535 X0 x X1
       grind)
    | exact resolve eq45847 eq246535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45847 eq246535
  have eq971579 : ∀ X0 X1 : G, x = (σ (M.op x (σ X0))) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq971439 X0 X1
       have i₂ := eq45969
       grind)
    | exact superpose eq45969 eq971439
    | (have j0 := eq971439 X0 X1
       grind)
    | exact resolve eq971439 eq45969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971439
  have eq971956 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ x = (σ (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq971579 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq971579
    | (have j0 := eq971579 (τ X0) X1
       grind)
    | exact resolve eq971579 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971579
  have eq1007287 : ∀ X0 X1 : G, x = (M.op (σ (M.op X0 X1)) (M.op (σ X0) (σ X1))) ∨ x = X0 ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq604043 X0 X1
       have i₂ := eq60633 X0 X1
       grind)
    | exact superpose eq60633 eq604043
    | (have j0 := eq604043 (M.op (σ (M.op X0 X1)) (M.op (σ X0) (σ X1))) X1
       have j1 := eq60633 (M.op (σ (M.op X0 X1)) (M.op (σ X0) (σ X1))) X1
       grind)
    | exact resolve eq604043 eq60633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60633 eq604043
  have eq1007414 : ∀ X0 X1 : G, x = (M.op (σ (M.op X0 X1)) (M.op (σ X0) (σ X1))) ∨ x = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1007287 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007287
  have eq1142967 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (k (τ y) X0) = (M.op (τ y) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq687167 y (σ x) X0
       grind)
    | exact superpose eq687167 eq14
    | (have j1 := eq687167 y x X0
       grind)
    | exact resolve eq14 eq687167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687167
  have eq1143010 : ∀ X0 : G, x ≠ (σ (M.op x y)) ∨ (k (τ y) X0) = (M.op (τ y) X0) := by
    intro X0
    first
    | (have i₁ := eq1142967 X0
       have i₂ := eq45969
       grind)
    | exact superpose eq45969 eq1142967
    | (have j0 := eq1142967 X0
       grind)
    | exact resolve eq1142967 eq45969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142967
  have eq1143159 : ∀ X0 : G, (k (τ y) X0) = (M.op (τ y) X0) := by
    intro X0
    first
    | (have j0 := eq1143010 X0
       have j1 := eq971956 y X0
       grind)
    | (have r₁ := eq1143010 X0
       have r₂ := eq971956 y x
       grind)
    | exact resolve eq1143010 eq971956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971956 eq1143010
  have eq1144063 : ∀ X0 : G, (k y (σ X0)) = (σ (M.op (τ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq1143159 X0
       grind)
    | exact superpose eq1143159 eq15
    | exact resolve eq15 eq1143159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq1144090 : ∀ X0 : G, (τ (k y X0)) = (M.op (τ y) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 y
       have i₂ := eq1143159 (τ X0)
       grind)
    | exact superpose eq1143159 eq31
    | exact resolve eq31 eq1143159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq1144310 : ∀ X0 : G, (τ (M.op y X0)) = (M.op (τ y) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1144090 X0
       have i₂ := eq128447 X0
       grind)
    | exact superpose eq128447 eq1144090
    | exact resolve eq1144090 eq128447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144090
  have eq1144329 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op (τ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq1144063 X0
       have i₂ := eq128447 (σ X0)
       grind)
    | exact superpose eq128447 eq1144063
    | exact resolve eq1144063 eq128447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128447 eq1144063
  have eq1145304 : ∀ X0 : G, (M.op x (τ X0)) = (M.op (τ (M.op y X0)) (τ y)) := by
    intro X0
    first
    | (have i₁ := eq55522 (τ y) (τ X0)
       have i₂ := eq1144310 X0
       grind)
    | exact superpose eq1144310 eq55522
    | exact resolve eq55522 eq1144310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1145306 : ∀ X0 : G, (τ X0) = (M.op x (M.op (τ (M.op y X0)) (τ y))) := by
    intro X0
    first
    | (have i₁ := eq55537 (τ y) (τ X0)
       have i₂ := eq1144310 X0
       grind)
    | exact superpose eq1144310 eq55537
    | exact resolve eq55537 eq1144310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144310
  have eq1146981 : y = (k (M.op y (σ (M.op x (τ y)))) y) := by
    first
    | (have i₁ := eq416407 y
       have i₂ := eq1144329 (M.op x (τ y))
       grind)
    | exact superpose eq1144329 eq416407
    | exact resolve eq416407 eq1144329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416407 eq1144329
  have eq1197320 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op x (M.op x (σ (M.op X0 X1)))) ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq55537 (σ (M.op X0 X1)) (M.op (σ X0) (σ X1))
       have i₂ := eq1007414 X0 X1
       grind)
    | exact superpose eq1007414 eq55537
    | (have j1 := eq1007414 X0 X1
       grind)
    | exact resolve eq55537 eq1007414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55537 eq1007414
  have eq1197323 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1197320 X0 X1
       have i₂ := eq55904 (σ (M.op X0 X1))
       grind)
    | exact superpose eq55904 eq1197320
    | (have j0 := eq1197320 X0 X1
       grind)
    | exact resolve eq1197320 eq55904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197320
  have eq1197578 : ∀ X0 X1 : G, (M.op (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ x = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1197323 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1197323
    | (have j0 := eq1197323 X1 X1
       grind)
    | exact resolve eq1197323 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197323
  have eq1198859 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 (τ X1))
       have i₂ := eq1197578 X1 X0
       grind)
    | exact superpose eq1197578 eq9
    | (have j1 := eq1197578 X0 X0
       grind)
    | exact resolve eq9 eq1197578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197578
  have eq1199079 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (τ X0) = x := by
    intro X0 X1
    first
    | (have i₁ := eq1198859 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1198859
    | (have j0 := eq1198859 (τ X0) X1
       grind)
    | exact resolve eq1198859 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198859
  have eq1203086 : ∀ X0 : G, (M.op x (τ X0)) = (τ (M.op (M.op y X0) y)) ∨ x = (τ (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq1145304 X0
       have i₂ := eq1199079 (M.op y X0) y
       grind)
    | exact superpose eq1199079 eq1145304
    | (have j1 := eq1199079 (M.op y X0) x
       grind)
    | exact resolve eq1145304 eq1199079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145304 eq1199079
  have eq1203463 : ∀ X0 : G, x = (τ (M.op y X0)) ∨ (M.op x (τ X0)) = (τ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1203086 X0
       have i₂ := eq55522 y X0
       grind)
    | exact superpose eq55522 eq1203086
    | (have j0 := eq1203086 X0
       grind)
    | exact resolve eq1203086 eq55522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55522 eq1203086
  have eq1238674 : ∀ X0 : G, (τ X0) = (M.op x (M.op x (τ y))) ∨ (M.op x (τ X0)) = (τ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1145306 X0
       have i₂ := eq1203463 X0
       grind)
    | exact superpose eq1203463 eq1145306
    | (have j1 := eq1203463 X0
       grind)
    | exact resolve eq1145306 eq1203463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145306 eq1203463
  have eq1238763 : ∀ X0 : G, (M.op x (τ X0)) = (τ (M.op x X0)) ∨ (τ X0) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq1238674 X0
       have i₂ := eq55904 (τ y)
       grind)
    | exact superpose eq55904 eq1238674
    | (have j0 := eq1238674 X0
       grind)
    | exact resolve eq1238674 eq55904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55904 eq1238674
  have eq1238958 : ∀ X0 : G, (M.op x X0) = (σ (M.op x (τ X0))) ∨ (τ X0) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op x X0)
       have i₂ := eq1238763 X0
       grind)
    | exact superpose eq1238763 eq10
    | (have j1 := eq1238763 X0
       grind)
    | exact resolve eq10 eq1238763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238763
  have eq1239074 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) ∨ (τ y) = X0 := by
    intro X0
    first
    | (have i₁ := eq1238958 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1238958
    | exact resolve eq1238958 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238958
  have eq1239205 : (M.op x (σ y)) ≠ (M.op x (σ y)) ∨ y = (τ y) := by
    first
    | (have i₁ := eq46777
       have i₂ := eq1239074 y
       grind)
    | exact superpose eq1239074 eq46777
    | (have j1 := eq1239074 y
       grind)
    | (have r₁ := eq46777
       have r₂ := eq1239074 y
       grind)
    | exact resolve eq46777 eq1239074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46777 eq1239074
  have eq1239310 : y = (τ y) := by grind
  clear eq1239205
  have eq1239596 : y = (k (M.op y (σ (M.op x y))) y) := by
    first
    | (have i₁ := eq1146981
       have i₂ := eq1239310
       grind)
    | exact superpose eq1239310 eq1146981
    | exact resolve eq1146981 eq1239310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146981
  have eq1239612 : y = (σ y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1239310
       grind)
    | exact superpose eq1239310 eq10
    | exact resolve eq10 eq1239310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1240065 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1239612
       grind)
    | exact superpose eq1239612 eq14
    | exact resolve eq14 eq1239612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1240471 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1240065
       have i₂ := eq45969
       grind)
    | exact superpose eq45969 eq1240065
    | exact resolve eq1240065 eq45969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45969 eq1240065
  have eq1246020 : (M.op x y) = (σ (M.op x y)) ∨ x = (τ (M.op y (σ (M.op x y)))) := by
    first
    | (have i₁ := eq603847 y (σ (M.op x y))
       have i₂ := eq1239596
       grind)
    | exact superpose eq1239596 eq603847
    | (have j0 := eq603847 y (σ (M.op x y))
       grind)
    | exact resolve eq603847 eq1239596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603847 eq1239596
  have eq1246057 : x = (τ (M.op y (σ (M.op x y)))) := by
    first
    | (have r₁ := eq1246020
       have r₂ := eq1240471
       grind)
    | exact resolve eq1246020 eq1240471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246020
  have eq1246084 : x = (k (τ y) (M.op x y)) := by
    first
    | (have i₁ := eq1246057
       have i₂ := eq131406 (M.op x y)
       grind)
    | exact superpose eq131406 eq1246057
    | exact resolve eq1246057 eq131406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131406 eq1246057
  have eq1246099 : x = (M.op (τ y) (M.op x y)) := by
    first
    | (have i₁ := eq1246084
       have i₂ := eq1143159 (M.op x y)
       grind)
    | exact superpose eq1143159 eq1246084
    | exact resolve eq1246084 eq1143159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143159 eq1246084
  have eq1246107 : x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq1246099
       have i₂ := eq1239310
       grind)
    | exact superpose eq1239310 eq1246099
    | exact resolve eq1246099 eq1239310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239310 eq1246099
  have eq1246148 : y = (M.op x y) := by
    first
    | (have i₁ := eq55524 y y
       have i₂ := eq1246107
       grind)
    | exact superpose eq1246107 eq55524
    | exact resolve eq55524 eq1246107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55524 eq1246107
  have eq1246965 : y ≠ (σ y) := by
    first
    | (have i₁ := eq1240471
       have i₂ := eq1246148
       grind)
    | exact superpose eq1246148 eq1240471
    | exact resolve eq1240471 eq1246148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240471 eq1246148
  have eq1247391 : False := by grind
  exact eq1247391

/-- `Equation978`: `x = y ◇ ((z ◇ z) ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation978 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law978 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law978.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X2) (M.op X0 X1))) = X0 := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) (M.op (M.op X3 X3) X0)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op (M.op X1 X1) (M.op X0 X2)) X3
       have i₂ := eq8 X0 X2 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op X1 X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X2 X2) (M.op X0 (M.op X1 X1)) X1
       have i₂ := eq8 X0 (M.op X1 X1) X2
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
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 x x X0
       have i₂ := eq19 x x X1
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) X0) = X3 ∨ (M.op X2 X3) = (k X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X2 X3
       have i₂ := eq19 X0 X1 X2
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 X2 X3
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) X0) = (k X2 (M.op (M.op X0 (M.op X1 X1)) X0)) := by
    intro X0 X1 X2
    grind
  have eq56 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X1 (M.op X1 X1)
       have i₂ := eq19 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq60 : ∀ X0 X2 : G, (M.op X0 X0) = (k X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq53 x X0 X2
       have i₂ := eq56 X0 x
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq62 : ∀ X0 X2 X3 : G, (M.op X0 X0) = X3 ∨ (M.op X2 X3) = (k X2 X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq51 X0 x X2 X3
       have i₂ := eq56 x X0
       grind)
    | exact superpose eq56 eq51
    | (have j0 := eq51 X0 x X2 X3
       grind)
    | exact resolve eq51 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq124 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X2) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 (M.op X1 X1) X2
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq8
    | exact resolve eq8 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq142 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X4) X3) = (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X5 X5) (M.op (M.op X2 X2) (M.op X3 X0)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq18 (M.op (M.op X2 X2) (M.op X3 X0)) X1 (M.op (M.op X4 X4) X3) X5
       have i₂ := eq18 X3 X2 X0 X4
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq182 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X4 X4) X3) = (M.op (M.op (M.op X1 X1) X0) (M.op X3 X0)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq142 X0 X1 x X3 X4 x
       have i₂ := eq124 (M.op X3 X0) x x
       grind)
    | exact superpose eq124 eq142
    | exact resolve eq142 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq326 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1 (M.op X0 X0)
       have i₂ := eq60 X0 (σ X1)
       grind)
    | exact superpose eq60 eq39
    | exact resolve eq39 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq415 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq50 (σ X0) X1
       grind)
    | (have i₁ := eq31 X0 X0
       have i₂ := eq50 X0 (σ X0)
       grind)
    | exact superpose eq50 eq31
    | exact resolve eq31 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq432 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  clear eq31
  have eq774 : ∀ X0 X1 : G, (τ (τ (M.op X0 X0))) = (k X1 (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1 (τ (M.op X0 X0))
       have i₂ := eq326 X0 (σ X1)
       grind)
    | exact superpose eq326 eq39
    | exact resolve eq39 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq326
  have eq2259 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X4) X2) = (M.op (M.op X1 X2) (M.op (M.op X3 X3) (M.op (M.op X0 X0) X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op (M.op X4 X4) X2) (M.op X1 X2) X3
       have i₂ := eq182 X2 X4 X1 X0
       grind)
    | exact superpose eq182 eq8
    | exact resolve eq8 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq2260 : ∀ X1 X2 X4 : G, (M.op (M.op X4 X4) X2) = (M.op (M.op X1 X2) X1) := by
    intro X1 X2 X4
    first
    | (have i₁ := eq2259 x X1 X2 x X4
       have i₂ := eq124 X1 x x
       grind)
    | exact superpose eq124 eq2259
    | exact resolve eq2259 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2259
  have eq2488 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X1) X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq124 X1 X2 x
       have i₂ := eq2260 X0 X1 x
       grind)
    | (have i₁ := eq124 X2 X1 X2
       have i₂ := eq2260 X2 X2 x
       grind)
    | exact superpose eq2260 eq124
    | exact resolve eq124 eq2260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq2260
  have eq4852 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq415 X1 (M.op X0 X0)
       have i₂ := eq60 X0 (M.op X0 X0)
       grind)
    | exact superpose eq60 eq415
    | (have j0 := eq415 X1 (M.op X0 X0)
       grind)
    | exact resolve eq415 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4857 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) ∨ (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq415 X1 (τ (τ (M.op X0 X0)))
       have i₂ := eq774 X0 (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq774 eq415
    | (have j0 := eq415 X1 (τ (τ (M.op X0 X0)))
       grind)
    | exact resolve eq415 eq774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq4952 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X1)) X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X1)
       have i₂ := eq415 X0 (τ X1)
       grind)
    | exact superpose eq415 eq17
    | (have j1 := eq415 X0 (τ X1)
       grind)
    | exact resolve eq17 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq415
  have eq4974 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq4857 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4857
  have eq4978 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4852 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4852
  have eq4989 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4952 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4952
    | (have j0 := eq4952 X0 X1
       grind)
    | exact resolve eq4952 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4952
  have eq5025 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4974 X0 X1
       have i₂ := eq10 (τ (M.op X0 X0))
       grind)
    | exact superpose eq10 eq4974
    | exact resolve eq4974 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4974
  have eq5035 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4989 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4989
    | (have j0 := eq4989 X0 X1
       grind)
    | exact resolve eq4989 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4989
  have eq5058 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq432
       have i₂ := eq62 X0 x y
       grind)
    | exact superpose eq62 eq432
    | (have j1 := eq62 (σ x) x (σ y)
       grind)
    | exact resolve eq432 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq432
  have eq5064 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq5058 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5058
  have eq5173 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (σ (M.op X0 X0)) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2488 X2 X2 X1
       have i₂ := eq4978 X0 X2
       grind)
    | exact superpose eq4978 eq2488
    | exact resolve eq2488 eq4978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2488 eq4978
  have eq30475 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 X1 X2
       have i₂ := eq5035 X2 X0
       grind)
    | exact superpose eq5035 eq50
    | (have j1 := eq5035 X1 X0
       grind)
    | exact resolve eq50 eq5035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq30754 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5035 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46085 : ∀ X0 X2 X3 : G, (k X2 X0) = X0 ∨ (M.op X3 X3) = (k X0 X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq60 X2 X2
       have i₂ := eq30475 X0 x X2
       grind)
    | (have i₁ := eq60 X0 X2
       have i₂ := eq30475 (M.op X0 X0) x X2
       grind)
    | exact superpose eq30475 eq60
    | (have j1 := eq30475 X0 X3 X2
       grind)
    | exact resolve eq60 eq30475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq30475
  have eq66856 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46085 X0 x X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46085
  have eq66862 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq66856 X0 X1
       have j1 := eq5035 X1 X0
       grind)
    | (have r₁ := eq66856 (k X1 X1) X0
       have r₂ := eq5035 X0 X1
       grind)
    | (have r₁ := eq66856 X1 X0
       have r₂ := eq5035 X0 X1
       grind)
    | (have r₁ := eq66856 (M.op X0 X0) X1
       have r₂ := eq5035 X0 (M.op X1 X1)
       grind)
    | exact resolve eq66856 eq5035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5035 eq66856
  have eq67900 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30754 X2 X1
       have i₂ := eq66862 X1 X0
       grind)
    | exact superpose eq66862 eq30754
    | (have j0 := eq30754 X2 X1
       grind)
    | (have r₁ := eq30754 X0 (M.op X1 X1)
       have r₂ := eq66862 (M.op X1 X1) X1
       grind)
    | exact resolve eq30754 eq66862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30754 eq66862
  have eq69448 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ y)) ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5025 (σ x) X0
       have i₂ := eq5064 X1
       grind)
    | exact superpose eq5064 eq5025
    | (have j1 := eq5064 X1
       grind)
    | exact resolve eq5025 eq5064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5025 eq5064
  have eq69767 : ∀ X0 X1 : G, (M.op X0 X0) = y ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq69448 X0 X1
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq69448
    | (have j0 := eq69448 X0 X0
       grind)
    | exact resolve eq69448 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69448
  have eq69776 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq69767 X0 X0
       have j1 := eq67900 X0 y X0
       grind)
    | (have r₁ := eq69767 X0 x
       have r₂ := eq67900 X0 y x
       grind)
    | (have r₁ := eq69767 X0 X0
       have r₂ := eq67900 X0 y x
       grind)
    | exact resolve eq69767 eq67900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67900 eq69767
  have eq70032 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 X0 X0
       have i₂ := eq69776 (M.op X0 X0)
       grind)
    | exact superpose eq69776 eq8
    | exact resolve eq8 eq69776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70038 : ∀ X0 : G, y = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5173 X0 (σ (M.op X0 X0)) (σ (M.op X0 X0))
       have i₂ := eq69776 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))
       grind)
    | exact superpose eq69776 eq5173
    | exact resolve eq5173 eq69776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5173
  have eq70125 : y = (σ y) := by
    first
    | (have i₁ := eq70038 x
       have i₂ := eq69776 x
       grind)
    | exact superpose eq69776 eq70038
    | exact resolve eq70038 eq69776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69776 eq70038
  have eq70822 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq70125
       grind)
    | exact superpose eq70125 eq14
    | exact resolve eq14 eq70125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70125
  have eq70856 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq70822
       have i₂ := eq70032 (σ x)
       grind)
    | exact superpose eq70032 eq70822
    | exact resolve eq70822 eq70032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70822
  have eq70866 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq70856
       have i₂ := eq70032 x
       grind)
    | exact superpose eq70032 eq70856
    | exact resolve eq70856 eq70032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70032 eq70856
  have eq70867 : False := by grind
  exact eq70867
