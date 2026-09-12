import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxx_y_pxy_Equation418 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq22 (M.op X0 X1)
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq41 : ∀ X0 : G, (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq40
    | exact resolve eq40 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq91 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq112 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq107 X0 X1
       have i₂ := eq22 (τ X1)
       grind)
    | exact superpose eq22 eq107
    | (have j0 := eq107 X0 X1
       grind)
    | exact resolve eq107 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq113 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0 X1
       have i₂ := eq22 (σ X1)
       grind)
    | exact superpose eq22 eq105
    | (have j0 := eq105 X0 X1
       grind)
    | exact resolve eq105 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq115 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq91
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq99 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq99
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq99 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq140 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq132 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq132
    | (have j0 := eq132 X0 X1
       grind)
    | exact resolve eq132 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq143 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq113 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq113
    | exact resolve eq113 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq143 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq143
    | (have j0 := eq143 X0 X1
       grind)
    | exact resolve eq143 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq502 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq157 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq157
    | exact resolve eq157 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq624 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq112 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq112
    | exact resolve eq112 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq659 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq624 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq624
    | (have j0 := eq624 X0 X1
       grind)
    | exact resolve eq624 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq4084 : (σ (M.op x y)) ≠ (σ x) ∨ (k x (τ (σ y))) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq140 x (σ y)
       grind)
    | exact superpose eq140 eq16
    | (have j1 := eq140 x (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq140 (M.op x y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq16 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4086 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) X1) = X1 ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq140 X0 X1
       grind)
    | exact superpose eq140 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq140 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq140 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq140 X0 (M.op (σ X0) X1)
       grind)
    | exact resolve eq13 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq4105 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4086 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4086
  have eq4112 : ∀ X0 X1 : G, (σ X0) = X1 ∨ (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4105 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq4105
    | (have j0 := eq4105 X0 X1
       grind)
    | exact resolve eq4105 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4105
  have eq4113 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4112 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4112
  have eq4114 : (σ (M.op x y)) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4084
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq4084
    | exact resolve eq4084 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4084
  have eq4564 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ X0 = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4113 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4113
    | exact resolve eq4113 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4611 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (σ X1) X0
       have i₂ := eq4113 X1 (σ X0)
       grind)
    | exact superpose eq4113 eq91
    | (have j1 := eq4113 X0 (σ X1)
       grind)
    | exact resolve eq91 eq4113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq4113
  have eq4673 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4611 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4611
    | (have j0 := eq4611 X0 X1
       grind)
    | exact resolve eq4611 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4611
  have eq4682 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4564 X0 X1
       have i₂ := eq115 X1 X0
       grind)
    | exact superpose eq115 eq4564
    | (have j0 := eq4564 X0 X1
       grind)
    | exact resolve eq4564 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq4564
  have eq4705 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4673 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4673
    | (have j0 := eq4673 X0 X1
       grind)
    | exact resolve eq4673 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4673
  have eq4712 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4705 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4705
    | (have j0 := eq4705 X0 X1
       grind)
    | exact resolve eq4705 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4705
  have eq4784 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq4682 X0 X1
       grind)
    | exact superpose eq4682 eq11
    | (have j1 := eq4682 X0 X1
       grind)
    | exact resolve eq11 eq4682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4682
  have eq4892 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4784 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq4784
    | (have j0 := eq4784 X0 X1
       grind)
    | exact resolve eq4784 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4784
  have eq4962 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq4892 (τ X0) X1
       grind)
    | exact superpose eq4892 eq18
    | (have j1 := eq4892 (τ X0) X1
       grind)
    | exact resolve eq18 eq4892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4892
  have eq5866 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq4712 X1 X0
       grind)
    | exact superpose eq4712 eq11
    | (have j1 := eq4712 X1 X0
       grind)
    | exact resolve eq11 eq4712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4712
  have eq6779 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5866 x y
       grind)
    | exact superpose eq5866 eq16
    | (have j1 := eq5866 x y
       grind)
    | exact resolve eq16 eq5866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5866
  have eq6889 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6779
       have i₂ := eq502 y x
       grind)
    | exact superpose eq502 eq6779
    | (have j1 := eq502 y (M.op x y)
       grind)
    | (have r₁ := eq6779
       have r₂ := eq502 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq6779
       have r₂ := eq502 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6779 eq502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502 eq6779
  have eq6894 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq6889
  have eq6922 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6894
       grind)
    | exact superpose eq6894 eq16
    | exact resolve eq16 eq6894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6894
  have eq6923 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6922
       have i₂ := eq22 (σ x)
       grind)
    | exact superpose eq22 eq6922
    | exact resolve eq6922 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6922
  have eq6924 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6923
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq6923
    | exact resolve eq6923 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6923
  have eq6925 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq6924
  have eq7158 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq25 x y
       have i₂ := eq6925
       grind)
    | exact superpose eq6925 eq25
    | exact resolve eq25 eq6925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7168 : x ≠ y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  have eq7331 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7158
       have i₂ := eq6925
       grind)
    | exact superpose eq6925 eq7158
    | exact resolve eq7158 eq6925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6925 eq7158
  have eq7350 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq7331
  have eq7353 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq7350
       have r₂ := eq7168
       grind)
    | exact resolve eq7350 eq7168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7168 eq7350
  have eq8360 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4962 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4962
    | exact resolve eq4962 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4962
  have eq8482 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8360 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8360
    | (have j0 := eq8360 X0 X1
       grind)
    | exact resolve eq8360 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8360
  have eq38009 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4114
       have i₂ := eq7353
       grind)
    | exact superpose eq7353 eq4114
    | exact resolve eq4114 eq7353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4114 eq7353
  have eq38015 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by grind
  clear eq38009
  have eq38016 : (σ x) = (σ y) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq38015
  have eq38024 : y = (τ (σ x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq38016
       grind)
    | exact superpose eq38016 eq10
    | exact resolve eq10 eq38016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38016
  have eq38130 : x = y ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq38024
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq38024
    | exact resolve eq38024 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38024
  have eq38411 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38130
       grind)
    | exact superpose eq38130 eq16
    | exact resolve eq16 eq38130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38130
  have eq38412 : (σ x) ≠ (σ (M.op x x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq38411
       have i₂ := eq22 (σ x)
       grind)
    | exact superpose eq22 eq38411
    | exact resolve eq38411 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38411
  have eq38413 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq38412
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq38412
    | exact resolve eq38412 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38412
  have eq38414 : (k x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq38413
  have eq38441 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq38414
       grind)
    | exact superpose eq38414 eq11
    | exact resolve eq11 eq38414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38414
  have eq38863 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38441
       grind)
    | exact superpose eq38441 eq16
    | exact resolve eq16 eq38441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38892 : (σ x) = (M.op (σ x) (M.op (σ x) (σ (k x y)))) := by
    first
    | (have i₁ := eq25 (σ x) (σ y)
       have i₂ := eq38441
       grind)
    | exact superpose eq38441 eq25
    | exact resolve eq25 eq38441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq39003 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq38863
       have i₂ := eq8482 x y
       grind)
    | exact superpose eq8482 eq38863
    | (have j1 := eq8482 x y
       grind)
    | (have r₁ := eq38863
       have r₂ := eq8482 x y
       grind)
    | (have r₁ := eq38863
       have r₂ := eq8482 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq38863
       have r₂ := eq8482 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq38863 eq8482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8482
  have eq39004 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq38863
       have i₂ := eq659 y x
       grind)
    | exact superpose eq659 eq38863
    | (have j1 := eq659 x y
       grind)
    | (have r₁ := eq38863
       have r₂ := eq659 y x
       grind)
    | (have r₁ := eq38863
       have r₂ := eq659 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq38863
       have r₂ := eq659 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq38863 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq39005 : x = y ∨ x = (M.op x y) := by grind
  clear eq39004
  have eq39006 : x = y ∨ y = (k x y) := by grind
  clear eq39003
  have eq39271 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq38863
       have i₂ := eq39005
       grind)
    | exact superpose eq39005 eq38863
    | exact resolve eq38863 eq39005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39005
  have eq39272 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39271
       have i₂ := eq41 x
       grind)
    | exact superpose eq41 eq39271
    | exact resolve eq39271 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39271
  have eq39276 : (σ x) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39272
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq39272
    | exact resolve eq39272 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39272
  have eq39277 : x = (M.op x y) := by grind
  clear eq39276
  have eq39664 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq38863
       have i₂ := eq39006
       grind)
    | exact superpose eq39006 eq38863
    | exact resolve eq38863 eq39006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39006
  have eq39668 : (σ x) ≠ (σ (M.op x x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq39664
       have i₂ := eq41 x
       grind)
    | exact superpose eq41 eq39664
    | exact resolve eq39664 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq39664
  have eq39672 : (σ x) ≠ (σ x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq39668
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq39668
    | exact resolve eq39668 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq39668
  have eq39673 : y = (k x y) := by grind
  clear eq39672
  have eq40142 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq38863
       have i₂ := eq39673
       grind)
    | exact superpose eq39673 eq38863
    | exact resolve eq38863 eq39673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38863
  have eq40182 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq40142
       have i₂ := eq39277
       grind)
    | exact superpose eq39277 eq40142
    | exact resolve eq40142 eq39277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39277 eq40142
  have eq40980 : (σ x) = (M.op (σ x) (σ (k x (k x y)))) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ (k x y))) := by
    first
    | (have i₁ := eq38892
       have i₂ := eq113 x (k x y)
       grind)
    | exact superpose eq113 eq38892
    | (have j1 := eq113 x (k x y)
       grind)
    | exact resolve eq38892 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq38892
  have eq41043 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ (k x y))) := by
    first
    | (have i₁ := eq40980
       have i₂ := eq39673
       grind)
    | exact superpose eq39673 eq40980
    | exact resolve eq40980 eq39673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40980
  have eq41044 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq41043
  have eq41060 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq41044
       have i₂ := eq39673
       grind)
    | exact superpose eq39673 eq41044
    | exact resolve eq41044 eq39673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41044
  have eq41072 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq41060
       have i₂ := eq38441
       grind)
    | exact superpose eq38441 eq41060
    | exact resolve eq41060 eq38441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38441 eq41060
  have eq41073 : (σ x) = (σ (k x y)) := by grind
  clear eq41072
  have eq41080 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq41073
       have i₂ := eq39673
       grind)
    | exact superpose eq39673 eq41073
    | exact resolve eq41073 eq39673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39673 eq41073
  have eq41086 : False := by grind
  exact eq41086

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_y_pyy_pxy_Equation418 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (k X0 X0) = X0 := by
    intro X0
    grind
  have eq40 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq36 (M.op X0 X1)
       grind)
    | exact superpose eq36 eq9
    | exact resolve eq9 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq36 X1
       grind)
    | exact superpose eq36 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq36 (σ X1)
       grind)
    | exact superpose eq36 eq87
    | (have j0 := eq87 X0 X1
       grind)
    | exact resolve eq87 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq95 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0 X1
       have i₂ := eq36 (σ X1)
       grind)
    | exact superpose eq36 eq101
    | (have j0 := eq101 X0 X1
       grind)
    | exact resolve eq101 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq126 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq92 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq92
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq92 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq92 X0 X1
       grind)
    | exact resolve eq13 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (M.op (σ X0) (M.op X2 (σ (k X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X2 (σ X1)
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq9
    | (have j1 := eq92 X0 X1
       grind)
    | exact resolve eq9 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq138 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq135 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq135 X0 X0
       have r₂ := eq13 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq135 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq135 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq140 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq126 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq126
    | (have j0 := eq126 X0 X1
       grind)
    | exact resolve eq126 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq141 : ∀ X0 X1 : G, (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq138 X0 X1
       have i₂ := eq36 (σ X1)
       grind)
    | exact superpose eq36 eq138
    | (have j0 := eq138 X0 X1
       grind)
    | exact resolve eq138 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq142 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq141 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq141
    | (have j0 := eq141 X0 X1
       grind)
    | exact resolve eq141 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq143 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq142 X0 X1
       have i₂ := eq36 (σ X1)
       grind)
    | exact superpose eq36 eq142
    | (have j0 := eq142 X0 X1
       grind)
    | exact resolve eq142 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq144 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq143 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq543 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq140 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq140
    | exact resolve eq140 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq1119 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (M.op X1 X1) = (k (τ X0) X1) ∨ (τ X0) = (M.op X1 X1) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq13
    | (have j0 := eq13 (τ X0) X1
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq91 X0 (M.op (τ X0) X1)
       grind)
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq1134 : ∀ X0 X1 : G, (M.op X1 X1) = (k (τ X0) X1) ∨ (τ X0) = (M.op X1 X1) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1119 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119
  have eq1139 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (τ X0) = (M.op X1 X1) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1134 X0 X1
       have i₂ := eq36 X1
       grind)
    | exact superpose eq36 eq1134
    | (have j0 := eq1134 X0 X1
       grind)
    | exact resolve eq1134 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134
  have eq1144 : ∀ X0 X1 : G, (τ X0) = X1 ∨ (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1139 X0 X1
       have i₂ := eq36 X1
       grind)
    | exact superpose eq36 eq1139
    | (have j0 := eq1139 X0 X1
       grind)
    | exact resolve eq1139 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1139
  have eq1145 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1144 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144
  have eq1967 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 (σ (k x y))))) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq136 x y X0
       grind)
    | exact superpose eq136 eq16
    | (have j1 := eq136 x y X0
       grind)
    | exact resolve eq16 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq3294 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1145 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1145
    | exact resolve eq1145 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145
  have eq3357 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3294 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3294
    | (have j0 := eq3294 X0 X1
       grind)
    | exact resolve eq3294 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3294
  have eq3502 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq3357 X0 X1
       grind)
    | exact superpose eq3357 eq10
    | (have j1 := eq3357 X0 X1
       grind)
    | exact resolve eq10 eq3357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3557 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3502 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq3502
    | (have j0 := eq3502 X0 X1
       grind)
    | exact resolve eq3502 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3502
  have eq3559 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3557 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3557
    | (have j0 := eq3557 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq3557 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3603 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq3557 (σ X0) X1
       grind)
    | exact superpose eq3557 eq30
    | (have j1 := eq3557 (σ X0) X1
       grind)
    | exact resolve eq30 eq3557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3557
  have eq6431 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X1) X0
       have i₂ := eq3603 X1 (σ X0)
       grind)
    | exact superpose eq3603 eq23
    | (have j1 := eq3603 X1 (σ X0)
       grind)
    | exact resolve eq23 eq3603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3603
  have eq6497 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6431 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq6431
    | (have j0 := eq6431 X0 X1
       grind)
    | exact resolve eq6431 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6431
  have eq6529 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6497 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6497
    | (have j0 := eq6497 X0 X1
       grind)
    | exact resolve eq6497 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6497
  have eq6536 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6529 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6529
    | (have j0 := eq6529 X0 X1
       grind)
    | exact resolve eq6529 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6529
  have eq6861 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (k (τ X0) X1) = X1 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6536 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6536
    | (have j0 := eq6536 X1 (τ X0)
       grind)
    | exact resolve eq6536 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6911 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq6536 X1 X0
       grind)
    | exact superpose eq6536 eq11
    | (have j1 := eq6536 X1 X0
       grind)
    | exact resolve eq11 eq6536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6536
  have eq7077 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = X1 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 (σ X1))
       have i₂ := eq6861 X0 X1
       grind)
    | exact superpose eq6861 eq11
    | (have j1 := eq6861 X0 X1
       grind)
    | exact resolve eq11 eq6861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6861
  have eq7155 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = X1 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7077 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq7077
    | (have j0 := eq7077 X0 X1
       grind)
    | exact resolve eq7077 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq7077
  have eq7172 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (τ X0) = (k (τ X1) (τ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7155 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7155
    | (have j0 := eq7155 X1 (τ X0)
       grind)
    | exact resolve eq7155 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7155
  have eq7289 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7172 X0 X1
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq7172
    | (have j0 := eq7172 X0 X1
       grind)
    | exact resolve eq7172 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7172
  have eq7391 : ∀ X0 X1 X2 : G, (k (τ X1) (τ X0)) = (τ (k X1 (k X2 X0))) ∨ (M.op X2 X0) = (k X2 X0) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq95 (k X2 X0) X1
       have i₂ := eq7289 X0 X2
       grind)
    | exact superpose eq7289 eq95
    | (have j1 := eq7289 X0 X2
       grind)
    | exact resolve eq95 eq7289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7289
  have eq7501 : ∀ X0 X1 X2 : G, (τ (k X1 X0)) = (τ (k X1 (k X2 X0))) ∨ (M.op X2 X0) = (k X2 X0) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7391 X0 X1 X2
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq7391
    | (have j0 := eq7391 X0 X1 X2
       grind)
    | exact resolve eq7391 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq7391
  have eq8105 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6911 x y
       grind)
    | exact superpose eq6911 eq16
    | (have j1 := eq6911 x y
       grind)
    | exact resolve eq16 eq6911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6911
  have eq8190 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8105
       have i₂ := eq543 y x
       grind)
    | exact superpose eq543 eq8105
    | (have j1 := eq543 y (M.op x y)
       grind)
    | (have r₁ := eq8105
       have r₂ := eq543 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq8105
       have r₂ := eq543 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq8105 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8192 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq8105
       have i₂ := eq3357 x y
       grind)
    | exact superpose eq3357 eq8105
    | (have j1 := eq3357 x y
       grind)
    | (have r₁ := eq8105
       have r₂ := eq3357 x y
       grind)
    | (have r₁ := eq8105
       have r₂ := eq3357 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq8105
       have r₂ := eq3357 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq8105 eq3357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3357 eq8105
  have eq8195 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8192
  have eq8196 : x = y ∨ (σ x) = (σ y) ∨ y = (k x y) := by grind
  clear eq8195
  have eq8198 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq8190
  have eq8437 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8196
       grind)
    | exact superpose eq8196 eq16
    | exact resolve eq16 eq8196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8196
  have eq8438 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq8437
       have i₂ := eq36 (σ x)
       grind)
    | exact superpose eq36 eq8437
    | exact resolve eq8437 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8437
  have eq8439 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq8438
       have i₂ := eq36 x
       grind)
    | exact superpose eq36 eq8438
    | exact resolve eq8438 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8438
  have eq8440 : y = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq8439
  have eq8632 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8198
       grind)
    | exact superpose eq8198 eq16
    | exact resolve eq16 eq8198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8198
  have eq8633 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8632
       have i₂ := eq36 (σ x)
       grind)
    | exact superpose eq36 eq8632
    | exact resolve eq8632 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8632
  have eq8634 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8633
       have i₂ := eq36 x
       grind)
    | exact superpose eq36 eq8633
    | exact resolve eq8633 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8633
  have eq8635 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq8634
  have eq8798 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq40 x y
       have i₂ := eq8635
       grind)
    | exact superpose eq8635 eq40
    | exact resolve eq40 eq8635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8811 : x ≠ y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  have eq8967 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8798
       have i₂ := eq8635
       grind)
    | exact superpose eq8635 eq8798
    | exact resolve eq8798 eq8635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8635 eq8798
  have eq8988 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq8967
  have eq8992 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8988
       have r₂ := eq8811
       grind)
    | exact resolve eq8988 eq8811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8811 eq8988
  have eq9713 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 (σ (k x y))))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1967 X0
       have i₂ := eq8992
       grind)
    | exact superpose eq8992 eq1967
    | (have j0 := eq1967 X0
       grind)
    | exact resolve eq1967 eq8992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1967 eq8992
  have eq9714 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 (σ (k x y))))) := by
    intro X0
    first
    | (have j0 := eq9713 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9713
  have eq9715 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 (σ (k x y))))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq9714 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9714
  have eq11196 : (σ x) = (M.op (σ x) (M.op (σ x) (σ (k x y)))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9715 (σ (k x y))
       have i₂ := eq36 (σ (k x y))
       grind)
    | exact superpose eq36 eq9715
    | exact resolve eq9715 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9715
  have eq11257 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11196
       have i₂ := eq8440
       grind)
    | exact superpose eq8440 eq11196
    | exact resolve eq11196 eq8440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8440 eq11196
  have eq11306 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by grind
  clear eq11257
  have eq27239 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k X0 (k X2 X1)) ∨ (k X2 X1) = (M.op X2 X1) ∨ X1 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X0 (k X2 X1))
       have i₂ := eq7501 X1 X0 X2
       grind)
    | exact superpose eq7501 eq11
    | (have j1 := eq7501 X1 X1 X2
       grind)
    | exact resolve eq11 eq7501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7501
  have eq27399 : ∀ X0 X1 X2 : G, (k X0 X1) = (k X0 (k X2 X1)) ∨ (k X2 X1) = (M.op X2 X1) ∨ X1 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27239 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq27239
    | (have j0 := eq27239 X0 X1 X2
       grind)
    | exact resolve eq27239 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27239
  have eq27541 : ∀ X0 X1 : G, (k X0 X1) = (k (k X0 X1) X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38 (k X0 X1)
       have i₂ := eq27399 (k X0 X1) X1 X0
       grind)
    | exact superpose eq27399 eq38
    | (have j1 := eq27399 X0 X1 X0
       grind)
    | exact resolve eq38 eq27399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq27399
  have eq28371 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (σ X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq144 (k X0 X1) X1
       have i₂ := eq27541 X0 X1
       grind)
    | exact superpose eq27541 eq144
    | (have j0 := eq144 X0 X1
       have j1 := eq27541 X0 X1
       grind)
    | (have r₁ := eq144 X0 X1
       have r₂ := eq27541 (σ X0) (σ (k X0 X1))
       grind)
    | (have r₁ := eq144 X0 X1
       have r₂ := eq27541 (σ (k X0 X1)) (σ X0)
       grind)
    | exact resolve eq144 eq27541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq27541
  have eq28541 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28371 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28371
  have eq28542 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28541 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28541
  have eq28762 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq28542 X1 (τ X0)
       grind)
    | exact superpose eq28542 eq19
    | (have j1 := eq28542 X1 (τ X0)
       grind)
    | exact resolve eq19 eq28542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28542
  have eq28920 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (k (σ X1) X0) = X0 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28762 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28762
    | (have j0 := eq28762 X0 X1
       grind)
    | exact resolve eq28762 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28762
  have eq29437 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k (σ X0) X1) = X1 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq28920 X1 X0
       grind)
    | exact superpose eq28920 eq19
    | (have j1 := eq28920 X1 X0
       grind)
    | exact resolve eq19 eq28920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq28920
  have eq30771 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29437 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29437
    | (have j0 := eq29437 X1 (σ X0)
       grind)
    | exact resolve eq29437 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29437
  have eq30926 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30771 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq30771
    | (have j0 := eq30771 X0 X1
       grind)
    | exact resolve eq30771 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30771
  have eq30930 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30926 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq30926
    | (have j0 := eq30926 X0 X1
       grind)
    | exact resolve eq30926 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30926
  have eq31123 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq30930 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42909 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3559 x y
       grind)
    | exact superpose eq3559 eq16
    | (have j1 := eq3559 x y
       grind)
    | exact resolve eq16 eq3559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3559
  have eq43128 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq42909
       have i₂ := eq30930 y x
       grind)
    | exact superpose eq30930 eq42909
    | (have j1 := eq30930 y x
       grind)
    | (have r₁ := eq42909
       have r₂ := eq30930 y x
       grind)
    | (have r₁ := eq42909
       have r₂ := eq30930 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq42909
       have r₂ := eq30930 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq42909 eq30930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30930 eq42909
  have eq43133 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) ∨ x = y := by grind
  clear eq43128
  have eq43137 : x = y ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq31123 x y
       grind)
    | (have r₁ := eq43133
       have r₂ := eq31123 x y
       grind)
    | exact resolve eq43133 eq31123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31123 eq43133
  have eq43441 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq43137
       grind)
    | exact superpose eq43137 eq16
    | exact resolve eq16 eq43137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43137
  have eq43442 : (σ x) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq43441
       have i₂ := eq36 (σ x)
       grind)
    | exact superpose eq36 eq43441
    | exact resolve eq43441 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43441
  have eq43443 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq43442
       have i₂ := eq36 x
       grind)
    | exact superpose eq36 eq43442
    | exact resolve eq43442 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43442
  have eq43444 : (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq43443
  have eq43446 : y = (τ (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq43444
       grind)
    | exact superpose eq43444 eq10
    | exact resolve eq10 eq43444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43444
  have eq43569 : x = y ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq43446
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq43446
    | exact resolve eq43446 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43446
  have eq43871 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq43569
       grind)
    | exact superpose eq43569 eq16
    | exact resolve eq16 eq43569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43569
  have eq43872 : (σ x) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq43871
       have i₂ := eq36 (σ x)
       grind)
    | exact superpose eq36 eq43871
    | exact resolve eq43871 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43871
  have eq43873 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq43872
       have i₂ := eq36 x
       grind)
    | exact superpose eq36 eq43872
    | exact resolve eq43872 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43872
  have eq43874 : (σ y) = (σ (k x y)) := by grind
  clear eq43873
  have eq43906 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq43874
       grind)
    | exact superpose eq43874 eq10
    | exact resolve eq10 eq43874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43913 : ∀ X0 : G, (k (τ X0) (k x y)) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq23 X0 (k x y)
       have i₂ := eq43874
       grind)
    | exact superpose eq43874 eq23
    | exact resolve eq23 eq43874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43923 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ y) = X0 ∨ (k (τ X0) (k x y)) = (τ (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq105 X0 (k x y)
       have i₂ := eq43874
       grind)
    | exact superpose eq43874 eq105
    | (have j0 := eq105 X0 y
       grind)
    | exact resolve eq105 eq43874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq43874
  have eq44024 : ∀ X0 : G, (k (τ X0) (k x y)) = (k (τ X0) y) := by
    intro X0
    first
    | (have i₁ := eq43913 X0
       have i₂ := eq23 X0 y
       grind)
    | exact superpose eq23 eq43913
    | exact resolve eq43913 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq43913
  have eq44031 : y = (k x y) := by
    first
    | (have i₁ := eq43906
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq43906
    | exact resolve eq43906 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43906
  have eq44328 : x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq543 y x
       have i₂ := eq44031
       grind)
    | exact superpose eq44031 eq543
    | (have j0 := eq543 x y
       grind)
    | exact resolve eq543 eq44031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq46791 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq44328
       grind)
    | exact superpose eq44328 eq16
    | exact resolve eq16 eq44328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44328
  have eq46798 : (σ x) ≠ (σ (M.op x x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq46791
       have i₂ := eq36 (σ x)
       grind)
    | exact superpose eq36 eq46791
    | exact resolve eq46791 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46791
  have eq46799 : (σ x) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq46798
       have i₂ := eq36 x
       grind)
    | exact superpose eq36 eq46798
    | exact resolve eq46798 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46798
  have eq46800 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq46799
  have eq47023 : x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq40 x y
       have i₂ := eq46800
       grind)
    | exact superpose eq46800 eq40
    | exact resolve eq40 eq46800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq47059 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq47417 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq47023
       have i₂ := eq46800
       grind)
    | exact superpose eq46800 eq47023
    | exact resolve eq47023 eq46800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46800 eq47023
  have eq47459 : x = y ∨ x = (M.op x y) := by grind
  clear eq47417
  have eq47466 : x = (M.op x y) := by
    first
    | (have r₁ := eq47459
       have r₂ := eq47059
       grind)
    | exact resolve eq47459 eq47059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47059 eq47459
  have eq91711 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (τ (σ x)) (k x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq43923 (σ x)
       grind)
    | exact superpose eq43923 eq16
    | (have j1 := eq43923 (σ x)
       grind)
    | exact resolve eq16 eq43923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43923
  have eq91807 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (τ (σ x)) (k x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq91711
       have i₂ := eq47466
       grind)
    | exact superpose eq47466 eq91711
    | exact resolve eq91711 eq47466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91711
  have eq91808 : (σ x) = (σ y) ∨ (k (τ (σ x)) (k x y)) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq91807
  have eq91850 : (k (τ (σ x)) y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq91808
       have i₂ := eq44024 (σ x)
       grind)
    | exact superpose eq44024 eq91808
    | exact resolve eq91808 eq44024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44024 eq91808
  have eq91867 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq91850
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq91850
    | exact resolve eq91850 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91850
  have eq91874 : (σ x) = (σ y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq91867
       have i₂ := eq44031
       grind)
    | exact superpose eq44031 eq91867
    | exact resolve eq91867 eq44031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44031 eq91867
  have eq92153 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq91874
       grind)
    | exact superpose eq91874 eq16
    | exact resolve eq16 eq91874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91874
  have eq92352 : (σ (M.op x y)) ≠ (σ x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq92153
       have i₂ := eq36 (σ x)
       grind)
    | exact superpose eq36 eq92153
    | exact resolve eq92153 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq92153
  have eq92353 : (σ x) ≠ (σ x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq92352
       have i₂ := eq47466
       grind)
    | exact superpose eq47466 eq92352
    | exact resolve eq92352 eq47466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92352
  have eq92354 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq92353
  have eq92422 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq92354
       grind)
    | exact superpose eq92354 eq11
    | exact resolve eq11 eq92354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92354
  have eq93166 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11306
       have i₂ := eq92422
       grind)
    | exact superpose eq92422 eq11306
    | exact resolve eq11306 eq92422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11306
  have eq93167 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq92422
       grind)
    | exact superpose eq92422 eq16
    | exact resolve eq16 eq92422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93384 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq93167
       have i₂ := eq47466
       grind)
    | exact superpose eq47466 eq93167
    | exact resolve eq93167 eq47466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47466 eq93167
  have eq93385 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq93166
       have i₂ := eq92422
       grind)
    | exact superpose eq92422 eq93166
    | exact resolve eq93166 eq92422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92422 eq93166
  have eq93386 : (σ x) = (σ y) := by grind
  clear eq93385
  have eq93434 : False := by grind
  exact eq93434

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_x_pyx_Equation418 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law418 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq110 (M.op X0 X1)
       grind)
    | exact superpose eq110 eq9
    | exact resolve eq9 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq505 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq506 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq539 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq506 X0 X1
       have i₂ := eq110 X1
       grind)
    | exact superpose eq110 eq506
    | (have j0 := eq506 X0 X1
       grind)
    | exact resolve eq506 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq540 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq505 X0 X1
       have i₂ := eq110 X1
       grind)
    | exact superpose eq110 eq505
    | (have j0 := eq505 X0 X1
       grind)
    | exact resolve eq505 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq803 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq539 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq539
    | exact resolve eq539 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq845 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq803 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq803
    | (have j0 := eq803 X0 X1
       grind)
    | exact resolve eq803 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq857 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq845 X0 X1
       grind)
    | exact superpose eq845 eq10
    | (have j1 := eq845 X0 X1
       grind)
    | exact resolve eq10 eq845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq892 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq857 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq857
    | (have j0 := eq857 X0 X1
       grind)
    | exact resolve eq857 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq2410 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq160 X0 (σ X1)
       have i₂ := eq540 X1 X0
       grind)
    | exact superpose eq540 eq160
    | (have j0 := eq160 (σ X1) X0
       have j1 := eq540 X1 X0
       grind)
    | (have r₁ := eq160 X1 (σ X0)
       have r₂ := eq540 X0 X1
       grind)
    | (have r₁ := eq160 (σ X0) X1
       have r₂ := eq540 X0 (M.op X1 (σ X0))
       grind)
    | exact resolve eq160 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq540
  have eq2423 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2410 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2410
  have eq2424 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2423 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2423
  have eq5055 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X1)
       have i₂ := eq2424 (σ X0) X1
       grind)
    | exact superpose eq2424 eq37
    | (have j1 := eq2424 (σ X1) X0
       grind)
    | exact resolve eq37 eq2424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2424
  have eq5120 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5055 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5055
    | (have j0 := eq5055 X0 X1
       grind)
    | exact resolve eq5055 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5055
  have eq5155 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5120 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5120
    | (have j0 := eq5120 X0 X1
       grind)
    | exact resolve eq5120 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5120
  have eq5168 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5155 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5155
    | (have j0 := eq5155 X0 X1
       grind)
    | exact resolve eq5155 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5155
  have eq5298 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq5168 X0 X1
       grind)
    | exact superpose eq5168 eq11
    | (have j1 := eq5168 X0 X1
       grind)
    | exact resolve eq11 eq5168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5168
  have eq6065 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5298 y x
       grind)
    | exact superpose eq5298 eq16
    | (have j1 := eq5298 y x
       grind)
    | exact resolve eq16 eq5298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5298
  have eq6141 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq6065
       have i₂ := eq892 x y
       grind)
    | exact superpose eq892 eq6065
    | (have j1 := eq892 x y
       grind)
    | (have r₁ := eq6065
       have r₂ := eq892 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq6065
       have r₂ := eq892 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq6065 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892 eq6065
  have eq6146 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6141
  have eq6147 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq6146
  have eq6153 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6147
       grind)
    | exact superpose eq6147 eq16
    | exact resolve eq16 eq6147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6147
  have eq6154 : y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6153
       have r₂ := eq22 x
       grind)
    | exact resolve eq6153 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6153
  have eq6157 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq120 x y
       have i₂ := eq6154
       grind)
    | exact superpose eq6154 eq120
    | exact resolve eq120 eq6154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq6173 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6157
       have i₂ := eq6154
       grind)
    | exact superpose eq6154 eq6157
    | exact resolve eq6157 eq6154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6157
  have eq6193 : x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq6173
  have eq6202 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6154
       have i₂ := eq6193
       grind)
    | exact superpose eq6193 eq6154
    | exact resolve eq6154 eq6193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6154 eq6193
  have eq6216 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq6202
  have eq6223 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6216
       grind)
    | exact superpose eq6216 eq16
    | exact resolve eq16 eq6216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6216
  have eq6224 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq6223
       have r₂ := eq22 x
       grind)
    | exact resolve eq6223 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6223
  have eq6225 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6224
       grind)
    | exact superpose eq6224 eq16
    | exact resolve eq16 eq6224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6226 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6224
       grind)
    | exact superpose eq6224 eq10
    | exact resolve eq10 eq6224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6224
  have eq6277 : x = y := by
    first
    | (have i₁ := eq6226
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6226
    | exact resolve eq6226 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6226
  have eq6278 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq6225
       have i₂ := eq110 (σ x)
       grind)
    | exact superpose eq110 eq6225
    | exact resolve eq6225 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6225
  have eq6282 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq6278
       have i₂ := eq6277
       grind)
    | exact superpose eq6277 eq6278
    | exact resolve eq6278 eq6277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6277 eq6278
  have eq6285 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq6282
       have i₂ := eq110 x
       grind)
    | exact superpose eq110 eq6282
    | exact resolve eq6282 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq6282
  have eq6286 : False := by grind
  exact eq6286

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = X then m(Y,X) else Y`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_pxx_pyx_y_Equation418 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) Law418 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq110 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq110 X0
       grind)
    | exact resolve eq13 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq168 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq175 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq169 X1 (τ X0)
       grind)
    | exact superpose eq169 eq19
    | (have j1 := eq169 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq176 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq169 (σ X1) (σ X0)
       grind)
    | exact superpose eq169 eq15
    | (have j1 := eq169 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq236 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq175 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq175
    | exact resolve eq175 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq262 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq236 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq236
    | (have j0 := eq236 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq236 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq828 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq176 x y
       grind)
    | exact superpose eq176 eq16
    | (have j1 := eq176 x y
       grind)
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq851 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq828
       have i₂ := eq262 x y
       grind)
    | exact superpose eq262 eq828
    | (have j1 := eq262 (σ x) (σ y)
       grind)
    | (have r₁ := eq828
       have r₂ := eq262 x y
       grind)
    | (have r₁ := eq828
       have r₂ := eq262 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq828
       have r₂ := eq262 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq828 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262 eq828
  have eq852 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq851
  have eq854 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq852
       grind)
    | exact superpose eq852 eq16
    | exact resolve eq16 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq855 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq854
       have r₂ := eq22 x
       grind)
    | exact resolve eq854 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq854
  have eq856 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq855
       grind)
    | exact superpose eq855 eq16
    | exact resolve eq16 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq857 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq855
       grind)
    | exact superpose eq855 eq10
    | exact resolve eq10 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq896 : x = y := by
    first
    | (have i₁ := eq857
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq857
    | exact resolve eq857 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq897 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq856
       have i₂ := eq110 (σ x)
       grind)
    | exact superpose eq110 eq856
    | exact resolve eq856 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq899 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq897
       have i₂ := eq896
       grind)
    | exact superpose eq896 eq897
    | exact resolve eq897 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896 eq897
  have eq900 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq899
       have i₂ := eq110 x
       grind)
    | exact superpose eq110 eq899
    | exact resolve eq899 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq899
  have eq901 : False := by grind
  exact eq901

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(X,X) = X then m(Y,X) else m(X,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_x_pyx_pxx_Equation418 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) Law418 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq76 X0
       grind)
    | exact resolve eq13 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq104 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq109 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq105 X1 (τ X0)
       grind)
    | exact superpose eq105 eq19
    | (have j1 := eq105 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq110 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq105 (σ X1) (σ X0)
       grind)
    | exact superpose eq105 eq15
    | (have j1 := eq105 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq147 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq109 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq109
    | exact resolve eq109 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq171 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq147 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq147
    | (have j0 := eq147 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq147 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq588 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq110 x y
       grind)
    | exact superpose eq110 eq16
    | (have j1 := eq110 x y
       grind)
    | exact resolve eq16 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq601 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq588
       have i₂ := eq171 x y
       grind)
    | exact superpose eq171 eq588
    | (have j1 := eq171 (σ x) (σ y)
       grind)
    | (have r₁ := eq588
       have r₂ := eq171 x y
       grind)
    | (have r₁ := eq588
       have r₂ := eq171 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq588
       have r₂ := eq171 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq588 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171 eq588
  have eq602 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq601
  have eq604 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq602
       grind)
    | exact superpose eq602 eq16
    | exact resolve eq16 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq605 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq604
       have i₂ := eq76 (σ x)
       grind)
    | exact superpose eq76 eq604
    | exact resolve eq604 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq606 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq605
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq605
    | exact resolve eq605 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq607 : (σ x) = (σ y) := by grind
  clear eq606
  have eq626 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq607
       grind)
    | exact superpose eq607 eq16
    | exact resolve eq16 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq627 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq607
       grind)
    | exact superpose eq607 eq10
    | exact resolve eq10 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq664 : x = y := by
    first
    | (have i₁ := eq627
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq627
    | exact resolve eq627 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq665 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq626
       have i₂ := eq76 (σ x)
       grind)
    | exact superpose eq76 eq626
    | exact resolve eq626 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq666 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq665
       have i₂ := eq664
       grind)
    | exact superpose eq664 eq665
    | exact resolve eq665 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664 eq665
  have eq667 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq666
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq666
    | exact resolve eq666 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq666
  have eq668 : False := by grind
  exact eq668

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(X,X) = X then m(Y,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_x_pyx_x_Equation418 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) Law418 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq76 X0
       grind)
    | exact resolve eq13 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq113 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq119 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq114 X1 (τ X0)
       grind)
    | exact superpose eq114 eq19
    | (have j1 := eq114 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq120 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq114 (σ X1) (σ X0)
       grind)
    | exact superpose eq114 eq15
    | (have j1 := eq114 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq157 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq119 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq119
    | exact resolve eq119 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq181 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq157 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq157
    | (have j0 := eq157 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq157 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq586 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq120 x y
       grind)
    | exact superpose eq120 eq16
    | (have j1 := eq120 x y
       grind)
    | exact resolve eq16 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq599 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq586
       have i₂ := eq181 x y
       grind)
    | exact superpose eq181 eq586
    | (have j1 := eq181 (σ x) (σ y)
       grind)
    | (have r₁ := eq586
       have r₂ := eq181 x y
       grind)
    | (have r₁ := eq586
       have r₂ := eq181 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq586
       have r₂ := eq181 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq586 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq586
  have eq600 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq599
  have eq602 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq600
       grind)
    | exact superpose eq600 eq16
    | exact resolve eq16 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq603 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq602
       have i₂ := eq76 (σ x)
       grind)
    | exact superpose eq76 eq602
    | exact resolve eq602 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq604 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq603
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq603
    | exact resolve eq603 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq605 : (σ x) = (σ y) := by grind
  clear eq604
  have eq624 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq605
       grind)
    | exact superpose eq605 eq16
    | exact resolve eq16 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq625 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq605
       grind)
    | exact superpose eq605 eq10
    | exact resolve eq10 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq662 : x = y := by
    first
    | (have i₁ := eq625
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq625
    | exact resolve eq625 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq663 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq624
       have i₂ := eq76 (σ x)
       grind)
    | exact superpose eq76 eq624
    | exact resolve eq624 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq664 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq663
       have i₂ := eq662
       grind)
    | exact superpose eq662 eq663
    | exact resolve eq663 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662 eq663
  have eq665 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq664
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq664
    | exact resolve eq664 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq664
  have eq666 : False := by grind
  exact eq666

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_pyy_pyx_Equation418 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law418 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq110 (M.op X0 X1)
       grind)
    | exact superpose eq110 eq9
    | exact resolve eq9 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 X1 : G, (τ X1) = (M.op X0 (τ X1)) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq928 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq165 x y
       grind)
    | exact superpose eq165 eq16
    | (have j1 := eq165 x y
       grind)
    | exact resolve eq16 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq4395 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (M.op X1 X1) = (k (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq167 X1 X0
       grind)
    | exact superpose eq167 eq13
    | (have j0 := eq13 (τ X0) X1
       have j1 := eq167 X1 X0
       grind)
    | (have r₁ := eq13 (τ X1) X0
       have r₂ := eq167 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) X1
       have r₂ := eq167 (M.op X1 (τ X1)) X1
       grind)
    | exact resolve eq13 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq4401 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (M.op X1 X1) = (k (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq4395 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4395
  have eq4402 : ∀ X0 X1 : G, (τ X0) = X1 ∨ (M.op X1 X1) = (k (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq4401 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4401
  have eq4404 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4402 X0 X1
       have i₂ := eq110 X1
       grind)
    | exact superpose eq110 eq4402
    | (have j0 := eq4402 X0 X1
       grind)
    | exact resolve eq4402 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4402
  have eq4420 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4404 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4404
    | exact resolve eq4404 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4404
  have eq4474 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4420 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4420
    | (have j0 := eq4420 X0 X1
       grind)
    | exact resolve eq4420 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4420
  have eq4531 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ X0 = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq4474 X1 X0
       grind)
    | exact superpose eq4474 eq10
    | (have j1 := eq4474 (k X1 X0) (τ (σ (M.op X0 X1)))
       grind)
    | exact resolve eq10 eq4474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4577 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4531 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq4531
    | (have j0 := eq4531 X0 X1
       grind)
    | exact resolve eq4531 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4531
  have eq4639 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ X1) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0
       have i₂ := eq4577 X0 (σ X1)
       grind)
    | exact superpose eq4577 eq37
    | (have j1 := eq4577 (k (σ X1) X0) X0
       grind)
    | exact resolve eq37 eq4577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq4577
  have eq5358 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X1) X0
       have i₂ := eq4639 (σ X0) X1
       grind)
    | exact superpose eq4639 eq28
    | (have j1 := eq4639 (σ X1) X0
       grind)
    | exact resolve eq28 eq4639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4639
  have eq5414 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5358 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5358
    | (have j0 := eq5358 X0 X1
       grind)
    | exact resolve eq5358 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5358
  have eq5450 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5414 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5414
    | (have j0 := eq5414 X0 X1
       grind)
    | exact resolve eq5414 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5414
  have eq5463 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5450 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5450
    | (have j0 := eq5450 X0 X1
       grind)
    | exact resolve eq5450 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5450
  have eq5765 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5463 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5463
    | (have j0 := eq5463 X1 (τ X0)
       grind)
    | exact resolve eq5463 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5789 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq5463 X1 X0
       grind)
    | exact superpose eq5463 eq11
    | (have j1 := eq5463 X1 X0
       grind)
    | exact resolve eq11 eq5463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5463
  have eq5898 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) ∨ (σ (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5765 X1 (τ X0)
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq5765
    | (have j0 := eq5765 X0 (τ X1)
       grind)
    | exact resolve eq5765 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq5765
  have eq6014 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (τ X1) = (τ (k X0 X1)) ∨ (σ (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5898 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5898
    | (have j0 := eq5898 X0 X1
       grind)
    | exact resolve eq5898 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5898
  have eq6054 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6014 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6014
    | (have j0 := eq6014 X0 X1
       grind)
    | exact resolve eq6014 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6014
  have eq6253 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq6054 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6054
  have eq6922 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5789 y x
       grind)
    | exact superpose eq5789 eq16
    | (have j1 := eq5789 y x
       grind)
    | exact resolve eq16 eq5789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5789
  have eq6996 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq6922
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq6922
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq6922
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq6922
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq6922 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6997 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k y x) := by
    first
    | (have i₁ := eq6922
       have i₂ := eq4474 y x
       grind)
    | exact superpose eq4474 eq6922
    | (have j1 := eq4474 x (k y x)
       grind)
    | (have r₁ := eq6922
       have r₂ := eq4474 y x
       grind)
    | (have r₁ := eq6922
       have r₂ := eq4474 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq6922
       have r₂ := eq4474 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq6922 eq4474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4474 eq6922
  have eq7000 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6997
  have eq7001 : x = y ∨ (σ x) = (σ y) ∨ x = (k y x) := by grind
  clear eq7000
  have eq7002 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq6996
  have eq7005 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7001
       grind)
    | exact superpose eq7001 eq16
    | exact resolve eq16 eq7001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7001
  have eq7006 : x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq7005
       have r₂ := eq22 x
       grind)
    | exact resolve eq7005 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7005
  have eq7016 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7002
       grind)
    | exact superpose eq7002 eq16
    | exact resolve eq16 eq7002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7002
  have eq7017 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq7016
       have r₂ := eq22 x
       grind)
    | exact resolve eq7016 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7016
  have eq7021 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq120 x y
       have i₂ := eq7017
       grind)
    | exact superpose eq7017 eq120
    | exact resolve eq120 eq7017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7035 : x ≠ y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  have eq7053 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq928
       have i₂ := eq7006
       grind)
    | exact superpose eq7006 eq928
    | exact resolve eq928 eq7006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928 eq7006
  have eq7062 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq7053
  have eq7063 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7021
       have i₂ := eq7017
       grind)
    | exact superpose eq7017 eq7021
    | exact resolve eq7021 eq7017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7017 eq7021
  have eq7083 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq7063
  have eq7086 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq7083
       have r₂ := eq7035
       grind)
    | exact resolve eq7083 eq7035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7035 eq7083
  have eq7102 : (τ x) ≠ (τ x) ∨ x = y ∨ (τ (k y x)) = (τ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6253 y x
       have i₂ := eq7086
       grind)
    | exact superpose eq7086 eq6253
    | (have j0 := eq6253 x y
       grind)
    | exact resolve eq6253 eq7086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6253 eq7086
  have eq7106 : x = y ∨ (τ (k y x)) = (τ x) ∨ (σ x) = (σ y) := by grind
  clear eq7102
  have eq7140 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (τ (k y x)) = (τ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7106
       grind)
    | exact superpose eq7106 eq16
    | exact resolve eq16 eq7106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7106
  have eq7141 : (σ x) = (σ y) ∨ (τ (k y x)) = (τ x) := by
    first
    | (have r₁ := eq7140
       have r₂ := eq22 x
       grind)
    | exact resolve eq7140 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7140
  have eq7143 : y = (τ (σ x)) ∨ (τ (k y x)) = (τ x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq7141
       grind)
    | exact superpose eq7141 eq10
    | exact resolve eq10 eq7141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7141
  have eq7197 : x = y ∨ (τ (k y x)) = (τ x) := by
    first
    | (have i₁ := eq7143
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7143
    | exact resolve eq7143 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7143
  have eq7204 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (τ (k y x)) = (τ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7197
       grind)
    | exact superpose eq7197 eq16
    | exact resolve eq16 eq7197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7197
  have eq7205 : (τ (k y x)) = (τ x) := by
    first
    | (have r₁ := eq7204
       have r₂ := eq22 x
       grind)
    | exact resolve eq7204 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7204
  have eq7218 : (k y x) = (σ (τ x)) := by
    first
    | (have i₁ := eq11 (k y x)
       have i₂ := eq7205
       grind)
    | exact superpose eq7205 eq11
    | exact resolve eq11 eq7205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7205
  have eq7336 : x = (k y x) := by
    first
    | (have i₁ := eq7218
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq7218
    | exact resolve eq7218 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7218
  have eq7351 : x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq7336
       grind)
    | exact superpose eq7336 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq7336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7336
  have eq8047 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7351
       grind)
    | exact superpose eq7351 eq16
    | exact resolve eq16 eq7351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7351
  have eq8059 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8047
       have r₂ := eq22 x
       grind)
    | exact resolve eq8047 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq8047
  have eq8070 : x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq120 x y
       have i₂ := eq8059
       grind)
    | exact superpose eq8059 eq120
    | exact resolve eq120 eq8059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8084 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq8121 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8070
       have i₂ := eq8059
       grind)
    | exact superpose eq8059 eq8070
    | exact resolve eq8070 eq8059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8059 eq8070
  have eq8143 : x = y ∨ x = (M.op x y) := by grind
  clear eq8121
  have eq8147 : x = (M.op x y) := by
    first
    | (have r₁ := eq8143
       have r₂ := eq8084
       grind)
    | exact resolve eq8143 eq8084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8084 eq8143
  have eq9859 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq7062
       have i₂ := eq8147
       grind)
    | exact superpose eq8147 eq7062
    | exact resolve eq7062 eq8147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7062
  have eq9860 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq9859
  have eq9881 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq120 (σ x) (σ y)
       have i₂ := eq9860
       grind)
    | exact superpose eq9860 eq120
    | exact resolve eq120 eq9860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq9930 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9881
       have i₂ := eq9860
       grind)
    | exact superpose eq9860 eq9881
    | exact resolve eq9881 eq9860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9881
  have eq9963 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq9930
  have eq9977 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9860
       have i₂ := eq9963
       grind)
    | exact superpose eq9963 eq9860
    | exact resolve eq9860 eq9963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9860 eq9963
  have eq10015 : (σ x) = (σ y) := by grind
  clear eq9977
  have eq10028 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10015
       grind)
    | exact superpose eq10015 eq16
    | exact resolve eq16 eq10015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10015
  have eq10087 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq10028
       have i₂ := eq110 (σ x)
       grind)
    | exact superpose eq110 eq10028
    | exact resolve eq10028 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq10028
  have eq10091 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq10087
       have i₂ := eq8147
       grind)
    | exact superpose eq8147 eq10087
    | exact resolve eq10087 eq8147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8147 eq10087
  have eq10092 : False := by grind
  exact eq10092

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxy_y_pxy_y_pxy_Equation419 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : (M.op x y) = (M.op x y) := by grind
  have eq18 : (M.op x y) = (M.op x y) := by grind
  clear eq17
  have eq19 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq20 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq19
  have eq21 : (σ x) = (σ x) := by grind
  have eq22 : (σ x) = (σ x) := by grind
  clear eq21
  have eq23 : (σ y) = (σ y) := by grind
  have eq24 : (σ y) = (σ y) := by grind
  clear eq23
  have eq25 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq26 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq25
  have eq27 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq35 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq44 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35
    | (have j0 := eq35 y
       grind)
    | exact resolve eq35 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq74 : y ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq82 x y
       grind)
    | exact superpose eq82 eq44
    | (have j1 := eq82 x y
       grind)
    | exact resolve eq44 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq113
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq113
    | exact resolve eq113 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq124 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq121
    | exact resolve eq121 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq124
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq124
    | exact resolve eq124 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq192 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq125 eq82
    | (have j0 := eq82 (σ x) (σ y)
       grind)
    | exact resolve eq82 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq192
    | exact resolve eq192 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq196 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq193
       have r₂ := eq27
       grind)
    | exact resolve eq193 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq198 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq196
    | exact resolve eq196 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq200 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq198 eq27
    | exact resolve eq27 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq198 eq75
    | (have r₁ := eq75
       have r₂ := eq198
       grind)
    | exact resolve eq75 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq198
  have eq358 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq357
  have eq361 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq358 eq125
    | exact resolve eq125 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq365 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq361
  have eq370 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq365
       have r₂ := eq200
       grind)
    | exact resolve eq365 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq365
  have eq375 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq370 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq377 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq82 (σ x) (σ y)
       grind)
    | (have r₁ := eq375
       have r₂ := eq82 (σ x) (σ y)
       grind)
    | exact resolve eq375 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq380 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq377
    | exact resolve eq377 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq433 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq380 eq125
    | exact resolve eq125 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq380
  have eq436 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq433
  have eq440 : y = (M.op x y) := by
    first
    | (have r₁ := eq436
       have r₂ := eq27
       grind)
    | exact resolve eq436 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq442 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq440 eq20
    | exact resolve eq20 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq445 : y ≠ y ∨ y = (M.op y x) ∨ y = (k x y) := by
    first
    | exact superpose eq440 eq74
    | (have r₁ := eq74
       have r₂ := eq440
       grind)
    | exact resolve eq74 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq450 : y = (k x y) ∨ y = (M.op y x) := by grind
  clear eq445
  have eq457 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq442
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq442
    | exact resolve eq442 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq461 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq457 eq26
    | exact resolve eq26 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq692 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq450
       grind)
    | exact superpose eq450 eq44
    | exact resolve eq44 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq699 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq457 eq692
    | exact resolve eq692 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq701 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq699
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq699
    | exact resolve eq699 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq702 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq457 eq701
    | exact resolve eq701 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq705 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq702 eq82
    | (have j0 := eq82 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq82 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq706 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by grind
  clear eq705
  have eq708 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq461 eq706
    | exact resolve eq706 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq711 : y = (M.op y x) := by
    first
    | (have r₁ := eq708
       have r₂ := eq27
       grind)
    | exact resolve eq708 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq725 : y ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq711
       grind)
    | exact superpose eq711 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq732 : (M.op x y) = (k x y) := by
    first
    | (have j1 := eq82 x y
       grind)
    | (have r₁ := eq725
       have r₂ := eq82 x y
       grind)
    | exact resolve eq725 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq735 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq732
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq732
    | exact resolve eq732 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq732
  have eq736 : y = (k x y) := by
    first
    | exact superpose eq440 eq735
    | exact resolve eq735 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440 eq735
  have eq746 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq736
       grind)
    | exact superpose eq736 eq44
    | exact resolve eq44 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq736
  have eq753 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq457 eq746
    | exact resolve eq746 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq755 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq753
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq753
    | exact resolve eq753 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq753
  have eq756 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq457 eq755
    | exact resolve eq755 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457 eq755
  have eq765 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq756 eq82
    | (have j0 := eq82 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq82 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq756
  have eq766 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq765
  have eq768 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq461 eq766
    | exact resolve eq766 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461 eq766
  have eq771 : False := by grind
  exact eq771
