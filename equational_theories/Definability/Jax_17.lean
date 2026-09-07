import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3620`: `x ◇ y = z ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_pxy_x_pxy_Equation3620 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3620 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3620.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq22 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X3
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X2 X3) X1) X0) X3) = (M.op X2 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op (M.op X2 X3) X1) X0) X3 X2
       have i₂ := eq9 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq62 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq76 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq74 (M.op X0 X1) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq74 (k X0 X1) (M.op X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq74 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq74 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq86 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq76 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq97 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq86 (σ X0)
       grind)
    | exact superpose eq86 eq15
    | exact resolve eq15 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq97 X0
       have i₂ := eq86 X0
       grind)
    | exact superpose eq86 eq97
    | exact resolve eq97 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq142 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 X0
       have i₂ := eq24 X1 X2 X0 X0
       grind)
    | (have i₁ := eq9 X2 X1 X0
       have i₂ := eq24 X0 X1 X2 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op (M.op X1 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X2 X1
       have i₂ := eq24 X1 X2 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq24 X0 X1 x x
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq273 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq432 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq433 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq432 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq456 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X3) X2) X1) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq142 X3 (M.op (M.op X0 X3) X2) X1
       have i₂ := eq25 X1 X2 X0 X3
       grind)
    | exact superpose eq25 eq142
    | exact resolve eq142 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq663 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (M.op X3 (M.op (M.op (M.op (M.op X0 X1) X0) X2) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq149 X3 (M.op (M.op X0 X1) X0) X2
       have i₂ := eq149 (M.op (M.op (M.op X0 X1) X0) X2) X0 X1
       grind)
    | exact superpose eq149 eq149
    | exact resolve eq149 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 X3)) = (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X3) X4) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq25 X4 X3 X0 (M.op (M.op X1 X2) X1)
       have i₂ := eq149 (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X3) X4) X1 X2
       grind)
    | exact superpose eq149 eq25
    | exact resolve eq25 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 X3)) = (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X1)) (M.op X2 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq693 X0 X1 X2 X3 X4
       have i₂ := eq456 (M.op X0 (M.op (M.op X1 X2) X1)) X2 X4 X3
       grind)
    | exact superpose eq456 eq693
    | exact resolve eq693 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456 eq693
  have eq729 : ∀ X0 X2 X3 : G, (M.op X3 X2) = (M.op X3 (M.op X0 (M.op X2 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq663 X0 x X2 X3
       have i₂ := eq25 X2 X0 X0 x
       grind)
    | exact superpose eq25 eq663
    | exact resolve eq663 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq663
  have eq742 : ∀ X0 X2 X3 X4 : G, (M.op X0 (M.op X4 X3)) = (M.op X3 (M.op (M.op X0 X2) (M.op X2 X4))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq708 X0 x X2 X3 X4
       have i₂ := eq149 X0 x X2
       grind)
    | exact superpose eq149 eq708
    | exact resolve eq708 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq708
  have eq903 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op (M.op X3 X1) X0) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq729 (M.op (M.op X3 X1) X0) X3 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq729
    | exact resolve eq729 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq942 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq142 (M.op X0 (M.op X1 X2)) X1 X2
       have i₂ := eq729 (M.op X1 X2) X0 (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq729 eq142
    | exact resolve eq142 eq729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq1005 : ∀ X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X3 X1) (M.op X1 X2)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq903 x X1 X2 X3
       have i₂ := eq742 (M.op X3 X1) x X2 X1
       grind)
    | exact superpose eq742 eq903
    | exact resolve eq903 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq903
  have eq1122 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq10
    | (have j1 := eq68 X0 X1
       grind)
    | exact resolve eq10 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq1207 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1122 X0 X1
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq1122
    | (have j0 := eq1122 X0 X1
       grind)
    | exact resolve eq1122 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122
  have eq1281 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1207 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1207
    | (have j0 := eq1207 X0 X1
       grind)
    | exact resolve eq1207 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207
  have eq1339 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1281 X0 X1
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq1281
    | (have j0 := eq1281 X0 X1
       grind)
    | exact resolve eq1281 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281
  have eq1606 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X2)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq942 X0 X2 (M.op X1 X2)
       have i₂ := eq729 X2 X1 X0
       grind)
    | exact superpose eq729 eq942
    | exact resolve eq942 eq729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729 eq942
  have eq1716 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq433 X0 (τ X1)
       grind)
    | exact superpose eq433 eq19
    | (have j1 := eq433 X0 (τ X1)
       grind)
    | exact resolve eq19 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq2177 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq1005 X0 X0 X0
       grind)
    | exact superpose eq1005 eq12
    | (have j0 := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq12 (M.op x x) X1
       have r₂ := eq1005 x x x
       grind)
    | exact resolve eq12 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005
  have eq2181 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq2177 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2177
  have eq2259 : ∀ X0 X1 : G, (σ (k (k (τ (σ X0)) X0) X1)) = (k (M.op (σ X0) (σ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) X0 X1
       have i₂ := eq86 (σ X0)
       grind)
    | exact superpose eq86 eq22
    | exact resolve eq22 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq2296 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) (σ X1)) = (σ (k (k (τ (σ X0)) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2259 X0 X1
       have i₂ := eq2181 (σ X0) (σ X1)
       grind)
    | exact superpose eq2181 eq2259
    | exact resolve eq2259 eq2181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2259
  have eq2302 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) (σ X1)) = (σ (k (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2296 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2296
    | exact resolve eq2296 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2296
  have eq2306 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) (σ X1)) = (σ (k (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2302 X0 X1
       have i₂ := eq86 X0
       grind)
    | exact superpose eq86 eq2302
    | exact resolve eq2302 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq2302
  have eq2308 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) (σ X1)) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2306 X0 X1
       have i₂ := eq2181 X0 X1
       grind)
    | exact superpose eq2181 eq2306
    | exact resolve eq2306 eq2181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2181 eq2306
  have eq2309 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) X1)) = (M.op (σ (M.op X0 X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2308 X0 X1
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq2308
    | exact resolve eq2308 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2308
  have eq5300 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op X1 (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1606 (σ X0) (σ X0) X1
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq1606
    | exact resolve eq1606 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5541 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) X1)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5300 X0 X1
       have i₂ := eq2309 X0 X0
       grind)
    | exact superpose eq2309 eq5300
    | exact resolve eq5300 eq2309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2309 eq5300
  have eq9622 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ X1) X2)) = (σ (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5541 X1 X2
       have i₂ := eq1606 X1 X1 X0
       grind)
    | exact superpose eq1606 eq5541
    | exact resolve eq5541 eq1606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1606 eq5541
  have eq31435 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9622 X1 X0 (σ X0)
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq9622
    | exact resolve eq9622 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq9622
  have eq39754 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1339 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1339
    | (have j0 := eq1339 X1 (τ X0)
       grind)
    | exact resolve eq1339 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339
  have eq40336 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq39754 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq39754
    | (have j0 := eq39754 X0 X1
       grind)
    | exact resolve eq39754 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq39754
  have eq40558 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq40336 X0 X1
       have j1 := eq273 X1 X0
       grind)
    | (have r₁ := eq40336 X0 X0
       have r₂ := eq273 X0 X1
       grind)
    | exact resolve eq40336 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273 eq40336
  have eq351492 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq40558 (σ X1) X0
       grind)
    | exact superpose eq40558 eq10
    | (have j1 := eq40558 (σ X1) X0
       grind)
    | exact resolve eq10 eq40558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40558
  have eq351738 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq351492 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq351492
    | (have j0 := eq351492 X0 X1
       grind)
    | exact resolve eq351492 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351492
  have eq353327 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1716 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1716
    | exact resolve eq1716 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1716
  have eq353365 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq353327 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq353327
    | (have j0 := eq353327 X0 X1
       grind)
    | exact resolve eq353327 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353327
  have eq355933 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq351738 x y
       grind)
    | exact superpose eq351738 eq16
    | (have j1 := eq351738 x y
       grind)
    | exact resolve eq16 eq351738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351738
  have eq356079 : y = (M.op x x) := by
    first
    | (have j1 := eq353365 y x
       grind)
    | (have r₁ := eq355933
       have r₂ := eq353365 y x
       grind)
    | exact resolve eq355933 eq353365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353365 eq355933
  have eq356291 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31435 x x
       have i₂ := eq356079
       grind)
    | exact superpose eq356079 eq31435
    | exact resolve eq31435 eq356079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31435 eq356079
  have eq356341 : False := by grind
  exact eq356341

/-- `Equation3620`: `x ◇ y = z ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_pyx_x_pyx_Equation3620 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3620 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3620.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq22 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X3
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X2 X3) X1) X0) X3) = (M.op X2 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op (M.op X2 X3) X1) X0) X3 X2
       have i₂ := eq9 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq62 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq76 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq74 (k X0 X1) (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq74 (M.op X1 X0) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq74 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq74 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq86 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq76 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq98 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq86 (σ X0)
       grind)
    | exact superpose eq86 eq15
    | exact resolve eq15 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq98 X0
       have i₂ := eq86 X0
       grind)
    | exact superpose eq86 eq98
    | exact resolve eq98 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq143 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 X0
       have i₂ := eq24 X1 X2 X0 X0
       grind)
    | (have i₁ := eq9 X2 X1 X0
       have i₂ := eq24 X0 X1 X2 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op (M.op X1 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X2 X1
       have i₂ := eq24 X1 X2 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq24 X0 X1 x x
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq273 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq433 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq434 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq433 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq456 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X3) X2) X1) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq143 X3 (M.op (M.op X0 X3) X2) X1
       have i₂ := eq25 X1 X2 X0 X3
       grind)
    | exact superpose eq25 eq143
    | exact resolve eq143 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (M.op X3 (M.op (M.op (M.op (M.op X0 X1) X0) X2) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq150 X3 (M.op (M.op X0 X1) X0) X2
       have i₂ := eq150 (M.op (M.op (M.op X0 X1) X0) X2) X0 X1
       grind)
    | exact superpose eq150 eq150
    | exact resolve eq150 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq692 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 X3)) = (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X3) X4) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq25 X4 X3 X0 (M.op (M.op X1 X2) X1)
       have i₂ := eq150 (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X3) X4) X1 X2
       grind)
    | exact superpose eq150 eq25
    | exact resolve eq25 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 X3)) = (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X1)) (M.op X2 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq692 X0 X1 X2 X3 X4
       have i₂ := eq456 (M.op X0 (M.op (M.op X1 X2) X1)) X2 X4 X3
       grind)
    | exact superpose eq456 eq692
    | exact resolve eq692 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456 eq692
  have eq728 : ∀ X0 X2 X3 : G, (M.op X3 X2) = (M.op X3 (M.op X0 (M.op X2 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq662 X0 x X2 X3
       have i₂ := eq25 X2 X0 X0 x
       grind)
    | exact superpose eq25 eq662
    | exact resolve eq662 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq662
  have eq741 : ∀ X0 X2 X3 X4 : G, (M.op X0 (M.op X4 X3)) = (M.op X3 (M.op (M.op X0 X2) (M.op X2 X4))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq707 X0 x X2 X3 X4
       have i₂ := eq150 X0 x X2
       grind)
    | exact superpose eq150 eq707
    | exact resolve eq707 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq707
  have eq894 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op (M.op X3 X1) X0) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq728 (M.op (M.op X3 X1) X0) X3 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq728
    | exact resolve eq728 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq930 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 (M.op X0 X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X2)) X2 X0
       have i₂ := eq728 (M.op X0 X2) X1 X0
       grind)
    | exact superpose eq728 eq9
    | exact resolve eq9 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq933 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq143 (M.op X0 (M.op X1 X2)) X1 X2
       have i₂ := eq728 (M.op X1 X2) X0 (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq728 eq143
    | exact resolve eq143 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq997 : ∀ X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X3 X1) (M.op X1 X2)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq894 x X1 X2 X3
       have i₂ := eq741 (M.op X3 X1) x X2 X1
       grind)
    | exact superpose eq741 eq894
    | exact resolve eq894 eq741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741 eq894
  have eq1120 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq68 X1 X0
       grind)
    | exact superpose eq68 eq10
    | (have j1 := eq68 X1 X0
       grind)
    | exact resolve eq10 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq1205 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1120 X0 X1
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq1120
    | (have j0 := eq1120 X0 X1
       grind)
    | exact resolve eq1120 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq1278 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1205 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1205
    | (have j0 := eq1205 X0 X1
       grind)
    | exact resolve eq1205 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205
  have eq1335 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1278 X0 X1
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq1278
    | (have j0 := eq1278 X0 X1
       grind)
    | exact resolve eq1278 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278
  have eq1404 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X1)) = (M.op X2 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X0 X1) X2
       have i₂ := eq930 X0 X2 X1
       grind)
    | exact superpose eq930 eq9
    | exact resolve eq9 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq1601 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X2)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq933 X0 X2 (M.op X1 X2)
       have i₂ := eq728 X2 X1 X0
       grind)
    | exact superpose eq728 eq933
    | exact resolve eq933 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933
  have eq1707 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq434 X1 (τ X0)
       grind)
    | exact superpose eq434 eq19
    | (have j1 := eq434 X1 (τ X0)
       grind)
    | exact resolve eq19 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq2166 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq997 X0 X0 X0
       grind)
    | exact superpose eq997 eq12
    | (have j0 := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq12 (M.op x x) X1
       have r₂ := eq997 x x x
       grind)
    | exact resolve eq12 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997
  have eq2170 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq2166 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2166
  have eq2245 : ∀ X0 X1 : G, (σ (k (k (τ (σ X0)) X0) X1)) = (k (M.op (σ X0) (σ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) X0 X1
       have i₂ := eq86 (σ X0)
       grind)
    | exact superpose eq86 eq22
    | exact resolve eq22 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq2282 : ∀ X0 X1 : G, (M.op (σ X1) (M.op (σ X0) (σ X0))) = (σ (k (k (τ (σ X0)) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2245 X0 X1
       have i₂ := eq2170 (σ X0) (σ X1)
       grind)
    | exact superpose eq2170 eq2245
    | exact resolve eq2245 eq2170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2245
  have eq2288 : ∀ X0 X1 : G, (M.op (σ X1) (M.op (σ X0) (σ X0))) = (σ (k (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2282 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2282
    | exact resolve eq2282 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2282
  have eq2292 : ∀ X0 X1 : G, (M.op (σ X1) (M.op (σ X0) (σ X0))) = (σ (k (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2288 X0 X1
       have i₂ := eq86 X0
       grind)
    | exact superpose eq86 eq2288
    | exact resolve eq2288 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq2288
  have eq2294 : ∀ X0 X1 : G, (M.op (σ X1) (M.op (σ X0) (σ X0))) = (σ (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2292 X0 X1
       have i₂ := eq2170 X0 X1
       grind)
    | exact superpose eq2170 eq2292
    | exact resolve eq2292 eq2170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2170 eq2292
  have eq2295 : ∀ X0 X1 : G, (σ (M.op X1 (M.op X0 X0))) = (M.op (σ X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2294 X0 X1
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq2294
    | exact resolve eq2294 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2294
  have eq4228 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op X1 (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1404 (σ X0) X1 (σ X0)
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq1404
    | exact resolve eq1404 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1404
  have eq4419 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) X1)) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4228 X0 X1
       have i₂ := eq2295 X0 X0
       grind)
    | exact superpose eq2295 eq4228
    | exact resolve eq4228 eq2295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2295 eq4228
  have eq8115 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ X1) X2)) = (σ (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4419 X1 X2
       have i₂ := eq1601 X0 X1 X1
       grind)
    | exact superpose eq1601 eq4419
    | exact resolve eq4419 eq1601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601
  have eq8199 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (τ (M.op X0 (M.op (σ X1) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 (M.op X1 X1))
       have i₂ := eq4419 X1 X0
       grind)
    | exact superpose eq4419 eq10
    | exact resolve eq10 eq4419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4419
  have eq23522 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (τ (M.op X0 (M.op (σ X1) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq728 X1 X1 X2
       have i₂ := eq8199 X0 X1
       grind)
    | exact superpose eq8199 eq728
    | exact resolve eq728 eq8199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq23618 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X2 X1) X2)) = (M.op (M.op (σ X1) (σ X1)) (τ (M.op X0 (M.op (σ (σ X1)) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8115 X2 X1 (M.op (σ X1) (σ X1))
       have i₂ := eq8199 X0 (σ X1)
       grind)
    | exact superpose eq8199 eq8115
    | exact resolve eq8115 eq8199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8115 eq8199
  have eq23643 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X2 X1) X2)) = (M.op (σ (M.op X1 X1)) (τ (M.op X0 (M.op (σ (σ X1)) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23618 X0 X1 X2
       have i₂ := eq107 X1
       grind)
    | exact superpose eq107 eq23618
    | exact resolve eq23618 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq23618
  have eq23824 : ∀ X1 X2 : G, (M.op (σ (M.op X1 X1)) (σ X1)) = (σ (M.op (M.op X2 X1) X2)) := by
    intro X1 X2
    first
    | (have i₁ := eq23643 x X1 X2
       have i₂ := eq23522 x (σ X1) (σ (M.op X1 X1))
       grind)
    | exact superpose eq23522 eq23643
    | exact resolve eq23643 eq23522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23522 eq23643
  have eq39054 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1335 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1335
    | (have j0 := eq1335 X1 (τ X0)
       grind)
    | exact resolve eq1335 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335
  have eq39679 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq39054 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq39054
    | (have j0 := eq39054 X0 X1
       grind)
    | exact resolve eq39054 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq39054
  have eq39891 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq39679 X0 X1
       have j1 := eq273 X1 X0
       grind)
    | (have r₁ := eq39679 X0 X0
       have r₂ := eq273 X0 X1
       grind)
    | exact resolve eq39679 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273 eq39679
  have eq344057 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq39891 (σ X1) X0
       grind)
    | exact superpose eq39891 eq10
    | (have j1 := eq39891 (σ X1) X0
       grind)
    | exact resolve eq10 eq39891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39891
  have eq344191 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq344057 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq344057
    | (have j0 := eq344057 X0 X1
       grind)
    | exact resolve eq344057 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344057
  have eq345278 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1707 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1707
    | exact resolve eq1707 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1707
  have eq345320 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq345278 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq345278
    | (have j0 := eq345278 X0 X1
       grind)
    | exact resolve eq345278 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345278
  have eq347289 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq344191 y x
       grind)
    | exact superpose eq344191 eq16
    | (have j1 := eq344191 y x
       grind)
    | exact resolve eq16 eq344191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344191
  have eq347430 : x = (M.op y y) := by
    first
    | (have j1 := eq345320 x y
       grind)
    | (have r₁ := eq347289
       have r₂ := eq345320 x y
       grind)
    | exact resolve eq347289 eq345320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345320 eq347289
  have eq347670 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23824 y y
       have i₂ := eq347430
       grind)
    | exact superpose eq347430 eq23824
    | exact resolve eq23824 eq347430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23824 eq347430
  have eq347721 : False := by grind
  exact eq347721

/-- `Equation3620`: `x ◇ y = z ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxx_pxy_x_pxx_pxy_Equation3620 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3620 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3620.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X3
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X2 X3) X1) X0) X3) = (M.op X2 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op (M.op X2 X3) X1) X0) X3 X2
       have i₂ := eq9 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq27 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq29 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq41 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X1) X2)) = (M.op X2 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq56 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X0 X1 X2
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq49
    | (have j0 := eq49 X0 X1 X2
       grind)
    | exact resolve eq49 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq71 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq29 (σ X0)
       grind)
    | exact superpose eq29 eq15
    | (have j1 := eq29 (σ X0)
       grind)
    | exact resolve eq15 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq119 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 X0
       have i₂ := eq20 X1 X2 X0 X0
       grind)
    | (have i₁ := eq9 X2 X1 X0
       have i₂ := eq20 X0 X1 X2 X0
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op (M.op X1 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X2 X1
       have i₂ := eq20 X1 X2 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq20 X0 X1 x x
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq156 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq168 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq156 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq156
    | exact resolve eq156 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq282 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X3) X2) X1) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq119 X3 (M.op (M.op X0 X3) X2) X1
       have i₂ := eq21 X1 X2 X0 X3
       grind)
    | exact superpose eq21 eq119
    | exact resolve eq119 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq54
    | (have j0 := eq54 (σ X0) (σ (k X0 X1))
       grind)
    | exact resolve eq54 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq369 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq366 X0 X1
       have j1 := eq56 X0 X1 x
       grind)
    | (have r₁ := eq366 X0 X1
       have r₂ := eq56 X0 X1 X0
       grind)
    | (have r₁ := eq366 X1 X0
       have r₂ := eq56 X0 X1 X1
       grind)
    | (have r₁ := eq366 X0 X0
       have r₂ := eq56 X0 (M.op X0 X0) x
       grind)
    | exact resolve eq366 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq366
  have eq402 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (M.op X3 (M.op (M.op (M.op (M.op X0 X1) X0) X2) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq127 X3 (M.op (M.op X0 X1) X0) X2
       have i₂ := eq127 (M.op (M.op (M.op X0 X1) X0) X2) X0 X1
       grind)
    | exact superpose eq127 eq127
    | exact resolve eq127 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq424 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 X3)) = (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X3) X4) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq21 X4 X3 X0 (M.op (M.op X1 X2) X1)
       have i₂ := eq127 (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X3) X4) X1 X2
       grind)
    | exact superpose eq127 eq21
    | exact resolve eq21 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 X3)) = (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X1)) (M.op X2 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq424 X0 X1 X2 X3 X4
       have i₂ := eq282 (M.op X0 (M.op (M.op X1 X2) X1)) X2 X4 X3
       grind)
    | exact superpose eq282 eq424
    | exact resolve eq424 eq282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282 eq424
  have eq447 : ∀ X0 X2 X3 : G, (M.op X3 X2) = (M.op X3 (M.op X0 (M.op X2 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq402 X0 x X2 X3
       have i₂ := eq21 X2 X0 X0 x
       grind)
    | exact superpose eq21 eq402
    | exact resolve eq402 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq402
  have eq457 : ∀ X0 X2 X3 X4 : G, (M.op X0 (M.op X4 X3)) = (M.op X3 (M.op (M.op X0 X2) (M.op X2 X4))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq437 X0 x X2 X3 X4
       have i₂ := eq127 X0 x X2
       grind)
    | exact superpose eq127 eq437
    | exact resolve eq437 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq437
  have eq646 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op (M.op X3 X1) X0) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq447 (M.op (M.op X3 X1) X0) X3 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq447
    | exact resolve eq447 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq678 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq119 (M.op X0 (M.op X1 X2)) X1 X2
       have i₂ := eq447 (M.op X1 X2) X0 (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq447 eq119
    | exact resolve eq119 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq447
  have eq726 : ∀ X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X3 X1) (M.op X1 X2)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq646 x X1 X2 X3
       have i₂ := eq457 (M.op X3 X1) x X2 X1
       grind)
    | exact superpose eq457 eq646
    | exact resolve eq646 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457 eq646
  have eq1159 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq1175 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1159 X0 X1
       have j1 := eq325 X0 X1
       grind)
    | (have r₁ := eq1159 X1 X1
       have r₂ := eq325 X1 X1
       grind)
    | (have r₁ := eq1159 X0 X1
       have r₂ := eq325 X0 X1
       grind)
    | (have r₁ := eq1159 X0 X1
       have r₂ := eq325 X0 (k X0 X1)
       grind)
    | exact resolve eq1159 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325 eq1159
  have eq1729 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  clear eq726
  have eq2887 : ∀ X0 : G, (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq27 X0
       have i₂ := eq369 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | exact superpose eq369 eq27
    | (have j1 := eq369 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | exact resolve eq27 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq4204 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1729 X0
       have i₂ := eq369 X0 X1
       grind)
    | (have i₁ := eq1729 X0
       have i₂ := eq369 X0 (M.op X0 X0)
       grind)
    | exact superpose eq369 eq1729
    | (have j1 := eq369 X1 X0
       grind)
    | exact resolve eq1729 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5969 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq369 X0 X0
       have i₂ := eq4204 X0 X1
       grind)
    | exact superpose eq4204 eq369
    | (have j0 := eq369 X1 X0
       have j1 := eq4204 X0 X1
       grind)
    | exact resolve eq369 eq4204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5977 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 (σ X0)
       have i₂ := eq4204 (σ X0) X1
       grind)
    | exact superpose eq4204 eq35
    | (have j1 := eq4204 (σ X0) X1
       grind)
    | exact resolve eq35 eq4204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq5992 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq4204 X1 (τ X0)
       grind)
    | exact superpose eq4204 eq18
    | (have j1 := eq4204 X1 X1
       grind)
    | exact resolve eq18 eq4204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5997 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq5969 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5969
  have eq6018 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5977 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5977
    | (have j0 := eq5977 X0 X1
       grind)
    | exact resolve eq5977 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5977
  have eq6962 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq71 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq7397 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq1175 X0 X1
       grind)
    | exact superpose eq1175 eq10
    | (have j1 := eq1175 X0 X1
       grind)
    | exact resolve eq10 eq1175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7427 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq168 X1
       have i₂ := eq1175 X1 X0
       grind)
    | exact superpose eq1175 eq168
    | (have j1 := eq1175 X1 X0
       grind)
    | exact resolve eq168 eq1175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq1175
  have eq7509 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7427 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7427
    | (have j0 := eq7427 X0 X1
       grind)
    | exact resolve eq7427 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7427
  have eq17395 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq6018 X1 (σ X0)
       grind)
    | exact superpose eq6018 eq15
    | (have j1 := eq6018 X1 X1
       grind)
    | exact resolve eq15 eq6018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6018
  have eq115434 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq6962 (M.op X0 X0)
       have i₂ := eq1729 X0
       grind)
    | exact superpose eq1729 eq6962
    | (have j0 := eq6962 (M.op X0 X0)
       grind)
    | exact resolve eq6962 eq1729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1729
  have eq115444 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq115434 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115434
  have eq117667 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op X1 (σ (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq678 X0 (σ (M.op X0 X0)) (σ (M.op X0 X0))
       have i₂ := eq115444 X0
       grind)
    | exact superpose eq115444 eq678
    | exact resolve eq678 eq115444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678 eq115444
  have eq130501 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7509 y x
       grind)
    | exact superpose eq7509 eq16
    | (have j1 := eq7509 y x
       grind)
    | exact resolve eq16 eq7509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7509
  have eq131564 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq130501
       have i₂ := eq369 x y
       grind)
    | exact superpose eq369 eq130501
    | (have j1 := eq369 x y
       grind)
    | exact resolve eq130501 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq130501
  have eq131574 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq131564
  have eq132917 : ∀ X0 : G, (M.op X0 y) = (M.op x (M.op x X0)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq131574
       grind)
    | exact superpose eq131574 eq9
    | exact resolve eq9 eq131574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153166 : (M.op x x) = (M.op y y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq132917 y
       have i₂ := eq131574
       grind)
    | exact superpose eq131574 eq132917
    | exact resolve eq132917 eq131574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131574 eq132917
  have eq153308 : (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq153166
  have eq154576 : (M.op x x) ≠ (M.op x x) ∨ y = (M.op x x) ∨ (M.op x x) = (k y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq153308
       grind)
    | exact superpose eq153308 eq13
    | (have j0 := eq13 x x
       grind)
    | exact resolve eq13 eq153308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153308
  have eq154643 : (M.op x x) ≠ (M.op x x) ∨ y = (M.op x x) ∨ (M.op x x) = (k y y) := by grind
  clear eq154576
  have eq154644 : (M.op x x) = (k y y) ∨ y = (M.op x x) := by grind
  clear eq154643
  have eq386645 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5992 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5992
    | (have j0 := eq5992 X0 X1
       grind)
    | exact resolve eq5992 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5992
  have eq386711 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq386645 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq386645
    | (have j0 := eq386645 X0 X1
       grind)
    | exact resolve eq386645 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386645
  have eq428199 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17395 x y
       grind)
    | exact superpose eq17395 eq16
    | (have j1 := eq17395 x y
       grind)
    | exact resolve eq16 eq17395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17395
  have eq428279 : y = (k y y) := by
    first
    | (have j1 := eq386711 x y
       grind)
    | (have r₁ := eq428199
       have r₂ := eq386711 x y
       grind)
    | exact resolve eq428199 eq386711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386711 eq428199
  have eq428533 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq154644
       have i₂ := eq428279
       grind)
    | exact superpose eq428279 eq154644
    | exact resolve eq154644 eq428279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154644
  have eq428540 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6962 y
       have i₂ := eq428279
       grind)
    | exact superpose eq428279 eq6962
    | (have j0 := eq6962 y
       grind)
    | exact resolve eq6962 eq428279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6962
  have eq428557 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq5997 y y
       have i₂ := eq428279
       grind)
    | exact superpose eq428279 eq5997
    | (have j0 := eq5997 y x
       grind)
    | exact resolve eq5997 eq428279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5997 eq428279
  have eq428560 : y = (M.op y y) := by grind
  clear eq428557
  have eq428572 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq428540
  have eq428578 : y = (M.op x x) := by grind
  clear eq428533
  have eq442386 : ∀ X0 : G, (M.op X0 x) = (M.op x (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq428578
       grind)
    | exact superpose eq428578 eq9
    | exact resolve eq9 eq428578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq442387 : y ≠ y ∨ x = y ∨ y = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq428578
       grind)
    | exact superpose eq428578 eq13
    | exact resolve eq13 eq428578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq442528 : y = (k x x) ∨ x = y := by grind
  clear eq442387
  have eq462272 : ∀ X0 : G, x = y ∨ (M.op X0 x) = (k X0 x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq4204 x X0
       have i₂ := eq442528
       grind)
    | exact superpose eq442528 eq4204
    | (have j0 := eq4204 x X0
       grind)
    | exact resolve eq4204 eq442528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4204 eq442528
  have eq462315 : ∀ X0 : G, (M.op X0 x) = (k X0 x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq462272 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462272
  have eq502008 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq442386 y
       have i₂ := eq428560
       grind)
    | exact superpose eq428560 eq442386
    | exact resolve eq442386 eq428560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428560 eq442386
  have eq514469 : ∀ X0 : G, (τ (σ y)) = X0 ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7397 y X0
       have i₂ := eq428572
       grind)
    | exact superpose eq428572 eq7397
    | (have j0 := eq7397 y X0
       grind)
    | exact resolve eq7397 eq428572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7397
  have eq514485 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq514469 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq514469
    | (have j0 := eq514469 X0
       grind)
    | exact resolve eq514469 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514469
  have eq519572 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (τ X0) x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq18 X0 x
       have i₂ := eq462315 (τ X0)
       grind)
    | exact superpose eq462315 eq18
    | exact resolve eq18 eq462315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq462315
  have eq560852 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq117667 (τ X0) X0
       have i₂ := eq2887 X0
       grind)
    | exact superpose eq2887 eq117667
    | (have j1 := eq2887 X0
       grind)
    | exact resolve eq117667 eq2887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2887 eq117667
  have eq560856 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq560852 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560852
  have eq560862 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq560856 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq560856
    | exact resolve eq560856 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560856
  have eq561050 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq560862 X0
       grind)
    | exact superpose eq560862 eq9
    | exact resolve eq9 eq560862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq584371 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op X0 x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq519572 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq519572
    | exact resolve eq519572 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519572
  have eq584386 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq584371 X0
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq584371
    | exact resolve eq584371 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584371
  have eq585265 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq561050 x X0
       have i₂ := eq428578
       grind)
    | exact superpose eq428578 eq561050
    | exact resolve eq561050 eq428578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428578 eq561050
  have eq585480 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq585265 (σ y)
       have i₂ := eq428572
       grind)
    | exact superpose eq428572 eq585265
    | exact resolve eq585265 eq428572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428572 eq585265
  have eq585763 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq514485 x
       have i₂ := eq585480
       grind)
    | exact superpose eq585480 eq514485
    | (have j0 := eq514485 x
       grind)
    | exact resolve eq514485 eq585480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514485 eq585480
  have eq592277 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq585763
       grind)
    | exact superpose eq585763 eq16
    | exact resolve eq16 eq585763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585763
  have eq592456 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq592277
       have i₂ := eq584386 y
       grind)
    | exact superpose eq584386 eq592277
    | exact resolve eq592277 eq584386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584386 eq592277
  have eq592462 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = y := by grind
  clear eq592456
  have eq592472 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq592462
       have i₂ := eq502008
       grind)
    | exact superpose eq502008 eq592462
    | exact resolve eq592462 eq502008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502008 eq592462
  have eq592473 : x = y := by grind
  clear eq592472
  have eq592628 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq592473
       grind)
    | exact superpose eq592473 eq16
    | exact resolve eq16 eq592473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592473
  have eq592861 : False := by grind
  exact eq592861

/-- `Equation3673`: `x ◇ x = (x ◇ y) ◇ (z ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pxx_x_pxy_Equation3673 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3673 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3673.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq44 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq44 (σ X0)
       grind)
    | exact superpose eq44 eq15
    | exact resolve eq15 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq49 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq49
    | exact resolve eq49 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq49
  have eq72 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq503 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq506 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq503 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq503 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq503 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq503 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq503 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq532 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq506 X0 (τ X1)
       grind)
    | exact superpose eq506 eq19
    | (have j1 := eq506 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq534 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq506 (σ X0) (σ X1)
       grind)
    | exact superpose eq506 eq15
    | (have j1 := eq506 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq38056 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq532 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq532
    | exact resolve eq532 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq38145 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38056 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq38056
    | (have j0 := eq38056 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq38056 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38056
  have eq162411 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq534 x y
       grind)
    | exact superpose eq534 eq16
    | (have j1 := eq534 x y
       grind)
    | exact resolve eq16 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq163022 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq162411
       have i₂ := eq38145 y x
       grind)
    | exact superpose eq38145 eq162411
    | (have j1 := eq38145 (σ x) (σ y)
       grind)
    | (have r₁ := eq162411
       have r₂ := eq38145 y x
       grind)
    | (have r₁ := eq162411
       have r₂ := eq38145 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq162411
       have r₂ := eq38145 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq162411 eq38145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38145 eq162411
  have eq163023 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq163022
  have eq164363 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq163023
       grind)
    | exact superpose eq163023 eq10
    | exact resolve eq10 eq163023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163023
  have eq164466 : x = y ∨ x = y := by
    first
    | (have i₁ := eq164363
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq164363
    | exact resolve eq164363 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164363
  have eq164467 : x = y := by grind
  clear eq164466
  have eq165678 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq164467
       grind)
    | exact superpose eq164467 eq16
    | exact resolve eq16 eq164467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164467
  have eq165679 : False := by grind
  exact eq165679

/-- `Equation3673`: `x ◇ x = (x ◇ y) ◇ (z ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxy_x_pxy_Equation3673 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3673 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3673.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq44 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq44 (σ X0)
       grind)
    | exact superpose eq44 eq15
    | exact resolve eq15 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq48 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq48
    | exact resolve eq48 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq48
  have eq71 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq76 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq76 (σ X0) (σ X1)
       grind)
    | exact superpose eq76 eq15
    | (have j1 := eq76 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq76 (τ X0) X1
       grind)
    | exact superpose eq76 eq18
    | (have j1 := eq76 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq76
  have eq2078 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq84 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq84
    | exact resolve eq84 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq2109 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2078 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2078
    | (have j0 := eq2078 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq2078 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2078
  have eq3191 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq83 x y
       grind)
    | exact superpose eq83 eq16
    | (have j1 := eq83 x y
       grind)
    | exact resolve eq16 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq13814 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3191
       have i₂ := eq2109 x y
       grind)
    | exact superpose eq2109 eq3191
    | (have j1 := eq2109 (σ x) (σ y)
       grind)
    | (have r₁ := eq3191
       have r₂ := eq2109 x y
       grind)
    | (have r₁ := eq3191
       have r₂ := eq2109 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq3191
       have r₂ := eq2109 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3191 eq2109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2109 eq3191
  have eq13815 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq13814
  have eq13901 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq13815
       grind)
    | exact superpose eq13815 eq10
    | exact resolve eq10 eq13815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13815
  have eq13946 : x = y ∨ x = y := by
    first
    | (have i₁ := eq13901
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq13901
    | exact resolve eq13901 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13901
  have eq13947 : x = y := by grind
  clear eq13946
  have eq14751 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13947
       grind)
    | exact superpose eq13947 eq16
    | exact resolve eq16 eq13947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13947
  have eq14752 : False := by grind
  exact eq14752

/-- `Equation3673`: `x ◇ x = (x ◇ y) ◇ (z ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_x_pxy_Equation3673 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3673 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3673.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X0 X1) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq42 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) ≠ (M.op X4 X4) ∨ (M.op X4 X0) = (k X4 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq12 X4 X0
       have i₂ := eq9 X0 X1 X2 X3
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X4 X0
       grind)
    | (have r₁ := eq12 X2 (M.op X2 X3)
       have r₂ := eq9 X2 X3 X2 X3
       grind)
    | (have r₁ := eq12 (M.op X2 X3) X2
       have r₂ := eq9 X2 X3 X2 X3
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq44 (σ X0)
       grind)
    | exact superpose eq44 eq15
    | exact resolve eq15 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq46
    | exact resolve eq46 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq46
  have eq75 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X1 X2) (M.op X3 X4)) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X1 X2 X3 X4
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X2 X3
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1 x x x
       have j1 := eq42 X1 X1 x x X0
       grind)
    | (have r₁ := eq75 (M.op x x) X1 x X1 x
       have r₂ := eq42 x x x x (M.op X1 x)
       grind)
    | (have r₁ := eq75 x X0 X1 x x
       have r₂ := eq42 X0 X1 x x x
       grind)
    | (have r₁ := eq75 (M.op (M.op X0 X1) (M.op x x)) (M.op x x) x x x
       have r₂ := eq42 X0 X1 x x x
       grind)
    | exact resolve eq75 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq75
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq80 (σ X0) (σ X1)
       grind)
    | exact superpose eq80 eq15
    | (have j1 := eq80 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq80 (τ X0) X1
       grind)
    | exact superpose eq80 eq18
    | (have j1 := eq80 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq80
  have eq1277 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq97 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq97
    | exact resolve eq97 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq1300 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1277 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1277
    | (have j0 := eq1277 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq1277 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277
  have eq2158 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq96 x y
       grind)
    | exact superpose eq96 eq16
    | (have j1 := eq96 x y
       grind)
    | exact resolve eq16 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq9125 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2158
       have i₂ := eq1300 x y
       grind)
    | exact superpose eq1300 eq2158
    | (have j1 := eq1300 (σ x) (σ y)
       grind)
    | (have r₁ := eq2158
       have r₂ := eq1300 x y
       grind)
    | (have r₁ := eq2158
       have r₂ := eq1300 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2158
       have r₂ := eq1300 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2158 eq1300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300 eq2158
  have eq9126 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq9125
  have eq9195 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq9126
       grind)
    | exact superpose eq9126 eq10
    | exact resolve eq10 eq9126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9126
  have eq9234 : x = y ∨ x = y := by
    first
    | (have i₁ := eq9195
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9195
    | exact resolve eq9195 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9195
  have eq9235 : x = y := by grind
  clear eq9234
  have eq9473 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9235
       grind)
    | exact superpose eq9235 eq16
    | exact resolve eq16 eq9235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9235
  have eq9474 : False := by grind
  exact eq9474

/-- `Equation3714`: `x ◇ y = (x ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_y_pyx_Equation3714 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3714 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3714.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq75 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq83 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k X0 (M.op X1 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1
       have i₂ := eq14 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 (M.op (M.op X0 X0) (M.op X1 X0)) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 (M.op X1 X1)
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq132 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq92 (σ X0) (σ X1)
       grind)
    | exact superpose eq92 eq15
    | (have j1 := eq92 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq92 X0 (τ X1)
       grind)
    | exact superpose eq92 eq19
    | (have j1 := eq92 X0 (τ X1)
       grind)
    | exact resolve eq19 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq139 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  clear eq92
  have eq332 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq1223 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq139 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq1224 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1223 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223
  have eq1278 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 (M.op X1 X1)
       have i₂ := eq9 X1 X1
       grind)
    | exact superpose eq9 eq84
    | (have j0 := eq84 X1 X0
       grind)
    | exact resolve eq84 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq1411 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1278 X0 X1
       have j1 := eq332 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq1278 X0 X1
       have r₂ := eq332 (M.op X0 X0) (M.op X1 X1)
       grind)
    | (have r₁ := eq1278 X0 X1
       have r₂ := eq332 (M.op X1 X1) (M.op X0 X0)
       grind)
    | (have r₁ := eq1278 X0 X1
       have r₂ := eq332 (M.op (M.op X0 X0) X1) (k X1 (M.op X0 X0))
       grind)
    | exact resolve eq1278 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332 eq1278
  have eq1432 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1224 (σ X0)
       grind)
    | exact superpose eq1224 eq15
    | exact resolve eq15 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1439 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1432 X0
       have i₂ := eq1224 X0
       grind)
    | exact superpose eq1224 eq1432
    | exact resolve eq1432 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224 eq1432
  have eq2323 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq1439 X0
       grind)
    | exact superpose eq1439 eq9
    | exact resolve eq9 eq1439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4688 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq134 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq134
    | exact resolve eq134 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq4857 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4688 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4688
    | (have j0 := eq4688 X0 X1
       grind)
    | exact resolve eq4688 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4688
  have eq9653 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq132 X0 X1
       grind)
    | exact superpose eq132 eq10
    | (have j1 := eq132 X0 X1
       grind)
    | exact resolve eq10 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq9860 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9653 X0 X1
       have i₂ := eq1439 X0
       grind)
    | exact superpose eq1439 eq9653
    | (have j0 := eq9653 X0 X1
       grind)
    | exact resolve eq9653 eq1439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9653
  have eq10016 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9860 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq9860
    | (have j0 := eq9860 X0 X1
       grind)
    | exact resolve eq9860 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9860
  have eq11167 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  clear eq1411
  have eq11287 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq11167 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11167
  have eq11360 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11287 (σ X0) X1
       have i₂ := eq1439 X0
       grind)
    | exact superpose eq1439 eq11287
    | exact resolve eq11287 eq1439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439
  have eq11864 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X1)) = (σ (k X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (M.op X0 X0)
       have i₂ := eq11360 X0 (σ X1)
       grind)
    | exact superpose eq11360 eq15
    | exact resolve eq15 eq11360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11360
  have eq11895 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X1)) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11864 X0 X1
       have i₂ := eq11287 X0 X1
       grind)
    | exact superpose eq11287 eq11864
    | exact resolve eq11864 eq11287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11287 eq11864
  have eq14800 : ∀ X0 X1 : G, (M.op (σ X1) (σ (M.op X0 X0))) = (M.op (σ (M.op X1 X1)) (σ (M.op (M.op X0 X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2323 X1 (σ (M.op X0 X0))
       have i₂ := eq11895 X0 X1
       grind)
    | exact superpose eq11895 eq2323
    | exact resolve eq2323 eq11895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2323
  have eq14914 : ∀ X0 X1 : G, (M.op (σ X1) (σ (M.op X0 X0))) = (σ (M.op (M.op X1 X1) (M.op (M.op X0 X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq14800 X0 X1
       have i₂ := eq11895 X1 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq11895 eq14800
    | exact resolve eq14800 eq11895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11895 eq14800
  have eq14960 : ∀ X0 X1 : G, (M.op (σ X1) (σ (M.op X0 X0))) = (σ (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14914 X0 X1
       have i₂ := eq9 X1 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq14914
    | exact resolve eq14914 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14914
  have eq66352 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10016 x y
       grind)
    | exact superpose eq10016 eq16
    | (have j1 := eq10016 x y
       grind)
    | exact resolve eq16 eq10016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10016
  have eq66671 : y = (M.op x x) := by
    first
    | (have j1 := eq4857 y x
       grind)
    | (have r₁ := eq66352
       have r₂ := eq4857 y x
       grind)
    | exact resolve eq66352 eq4857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4857 eq66352
  have eq67634 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14960 x x
       have i₂ := eq66671
       grind)
    | exact superpose eq66671 eq14960
    | exact resolve eq14960 eq66671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14960 eq66671
  have eq99482 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67634 x
       grind)
    | exact superpose eq67634 eq16
    | (have r₁ := eq16
       have r₂ := eq67634 x
       grind)
    | exact resolve eq16 eq67634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67634
  have eq99655 : False := by grind
  exact eq99655

/-- `Equation3714`: `x ◇ y = (x ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pyx_y_pyx_Equation3714 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3714 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3714.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq65 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq69 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op X2 X1)) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq71 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq71 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq71 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq77 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op X2 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq69 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq69 X0 X1 X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq69 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq69 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq226 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = (M.op X2 (M.op X0 X1)) ∨ (M.op (M.op X1 X0) X2) = (k X2 (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq77 X2 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq77
    | (have j0 := eq77 X2 (M.op X1 X0) X2
       grind)
    | exact resolve eq77 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq77 X0 X0 X0
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq77
    | (have j0 := eq77 X1 X0 X2
       have j1 := eq75 X1 X0
       grind)
    | exact resolve eq77 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq77
  have eq248 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq228 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq228 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq228 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq278 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq248 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq279 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq278 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq319 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq279 (σ X0)
       grind)
    | exact superpose eq279 eq15
    | exact resolve eq15 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq326 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq319 X0
       have i₂ := eq279 X0
       grind)
    | exact superpose eq279 eq319
    | exact resolve eq319 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279 eq319
  have eq428 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq326 X0
       grind)
    | exact superpose eq326 eq9
    | exact resolve eq9 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq65 X0 X1
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq65 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq65 X1 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq65 X0 X1
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq541 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq530 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq566 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq541 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq541
    | (have j0 := eq541 X0 X1
       grind)
    | exact resolve eq541 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq567 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq566 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq628 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq567 X0 X1
       have i₂ := eq326 X0
       grind)
    | exact superpose eq326 eq567
    | (have j0 := eq567 X0 X1
       grind)
    | exact resolve eq567 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq2910 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq628 X1 X0
       grind)
    | (have i₁ := eq10 X1
       have i₂ := eq628 X0 X1
       grind)
    | exact superpose eq628 eq10
    | (have j1 := eq628 X1 X0
       grind)
    | exact resolve eq10 eq628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq3012 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2910 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2910
    | (have j0 := eq2910 X0 X1
       grind)
    | exact resolve eq2910 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2910
  have eq5075 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3012 y x
       grind)
    | exact superpose eq3012 eq16
    | (have j1 := eq3012 y x
       grind)
    | exact resolve eq16 eq3012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3012
  have eq5550 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq5075
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq5075
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq5075 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5576 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq5550
  have eq5577 : x = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq5576
  have eq6438 : x ≠ x ∨ (M.op x y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq5577
       grind)
    | exact superpose eq5577 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq5577
       grind)
    | exact resolve eq12 eq5577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5577
  have eq6447 : (M.op x y) = (k y x) ∨ y = (M.op x x) := by grind
  clear eq6438
  have eq7788 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) X1) ∨ (M.op X1 (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq226 (σ X0) (σ X0) x
       have i₂ := eq326 X0
       grind)
    | exact superpose eq326 eq226
    | exact resolve eq226 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7812 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X1 X1)) ∨ (M.op (M.op X1 X1) X0) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1
       have i₂ := eq226 X1 X1 X0
       grind)
    | (have i₁ := eq9 X1 X0
       have i₂ := eq226 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq226 eq9
    | (have j1 := eq226 X1 X1 X0
       grind)
    | exact resolve eq9 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq7943 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq7812 X0 X1
       have j1 := eq12 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq7812 X0 X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact resolve eq7812 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7812
  have eq7954 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (k X1 (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7788 X0 X1
       have i₂ := eq326 (M.op X0 X0)
       grind)
    | exact superpose eq326 eq7788
    | (have j0 := eq7788 X0 X1
       grind)
    | exact resolve eq7788 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326 eq7788
  have eq8017 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) ∨ (k X1 (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7954 X0 X1
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq7954
    | (have j0 := eq7954 X0 X1
       grind)
    | exact resolve eq7954 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7954
  have eq8040 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq8017 X0 X1
       have j1 := eq12 X1 (σ (M.op X0 X0))
       grind)
    | (have r₁ := eq8017 X0 X0
       have r₂ := eq12 X0 (σ (M.op X0 X0))
       grind)
    | exact resolve eq8017 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8017
  have eq8286 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5075
       have i₂ := eq6447
       grind)
    | exact superpose eq6447 eq5075
    | exact resolve eq5075 eq6447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5075 eq6447
  have eq8287 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq8286
  have eq8288 : y = (M.op x x) := by grind
  clear eq8287
  have eq8388 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq9 x X0
       have i₂ := eq8288
       grind)
    | exact superpose eq8288 eq9
    | exact resolve eq9 eq8288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8399 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq428 x X0
       have i₂ := eq8288
       grind)
    | exact superpose eq8288 eq428
    | exact resolve eq428 eq8288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq8402 : ∀ X0 : G, (M.op y X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq7943 X0 x
       have i₂ := eq8288
       grind)
    | exact superpose eq8288 eq7943
    | exact resolve eq7943 eq8288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7943
  have eq8403 : y = (M.op y y) := by
    first
    | (have i₁ := eq9 x x
       have i₂ := eq8288
       grind)
    | exact superpose eq8288 eq9
    | exact resolve eq9 eq8288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8288
  have eq25892 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq8040 y x
       have i₂ := eq8403
       grind)
    | exact superpose eq8403 eq8040
    | exact resolve eq8040 eq8403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8040 eq8403
  have eq27738 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq25892 (σ X0)
       grind)
    | exact superpose eq25892 eq15
    | exact resolve eq15 eq25892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25892
  have eq27767 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq27738 X0
       have i₂ := eq8402 X0
       grind)
    | exact superpose eq8402 eq27738
    | exact resolve eq27738 eq8402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8402 eq27738
  have eq29159 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op y x))) := by
    first
    | (have i₁ := eq8399 (σ y)
       have i₂ := eq27767 x
       grind)
    | exact superpose eq27767 eq8399
    | exact resolve eq8399 eq27767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8399
  have eq29284 : (M.op (σ x) (σ y)) = (σ (M.op y (M.op y x))) := by
    first
    | (have i₁ := eq29159
       have i₂ := eq27767 (M.op y x)
       grind)
    | exact superpose eq27767 eq29159
    | exact resolve eq29159 eq27767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27767 eq29159
  have eq29335 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29284
       have i₂ := eq8388 y
       grind)
    | exact superpose eq8388 eq29284
    | exact resolve eq29284 eq8388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8388 eq29284
  have eq29348 : False := by grind
  exact eq29348
