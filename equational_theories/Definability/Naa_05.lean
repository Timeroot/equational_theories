import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3607`: `x ◇ y = z ◇ ((y ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_pyx_x_pyx_Equation3607 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3607 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3607.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X2) X0)) := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq21 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq26 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq27 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) (τ X1)) ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq35 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq26 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | (have j0 := eq26 X0
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq36 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22
    | exact resolve eq22 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq612 : ∀ X0 X1 : G, (τ X1) ≠ X0 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq21 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq1728 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (τ X1) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1
       have i₂ := eq27 X0 X1
       grind)
    | (have i₁ := eq35 X0
       have i₂ := eq27 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact superpose eq27 eq35
    | (have j0 := eq35 X1
       have j1 := eq27 X0 X1
       grind)
    | exact resolve eq35 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1747 : ∀ X0 X1 : G, (τ X0) ≠ X1 ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq27 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq1777 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1728 X0 X1
       have j1 := eq1747 X1 X0
       grind)
    | (have r₁ := eq1728 X0 (τ X0)
       have r₂ := eq1747 X0 (k (τ X0) (σ X0))
       grind)
    | (have r₁ := eq1728 X1 X0
       have r₂ := eq1747 X0 X1
       grind)
    | (have r₁ := eq1728 (τ X0) X1
       have r₂ := eq1747 X0 (τ X1)
       grind)
    | exact resolve eq1728 eq1747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1728 eq1747
  have eq8098 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq612 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq612
    | (have j0 := eq612 X1 X1
       grind)
    | (have r₁ := eq612 X0 (σ X0)
       have r₂ := eq10 X0
       grind)
    | (have r₁ := eq612 (τ (σ (τ X1))) X1
       have r₂ := eq10 (τ X1)
       grind)
    | exact resolve eq612 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq8119 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8098 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq8098
    | (have j0 := eq8098 X0 X1
       grind)
    | (have r₁ := eq8098 (σ (k X0 X1)) (k (σ X0) (σ X1))
       have r₂ := eq15 X0 X1
       grind)
    | (have r₁ := eq8098 (k (σ X0) (σ X1)) (σ (k X0 X1))
       have r₂ := eq15 X0 X1
       grind)
    | exact resolve eq8098 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8098
  have eq11082 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq8119 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8119
  have eq11105 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq11082 X0
       grind)
    | exact superpose eq11082 eq10
    | (have j1 := eq11082 X0
       grind)
    | exact resolve eq10 eq11082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11082
  have eq11145 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11105 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq11105
    | (have j0 := eq11105 X0
       grind)
    | exact resolve eq11105 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11105
  have eq11155 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11145 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq11145 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq11145 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11145
  have eq13082 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq11155 (σ X0)
       grind)
    | exact superpose eq11155 eq15
    | exact resolve eq15 eq11155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13089 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0 X0
       have i₂ := eq11155 (τ X0)
       grind)
    | exact superpose eq11155 eq36
    | exact resolve eq36 eq11155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq13101 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13089 X0
       have i₂ := eq11155 X0
       grind)
    | exact superpose eq11155 eq13089
    | exact resolve eq13089 eq11155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13089
  have eq13108 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13082 X0
       have i₂ := eq11155 X0
       grind)
    | exact superpose eq11155 eq13082
    | exact resolve eq13082 eq11155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13082
  have eq13162 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (τ (M.op X1 X1)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1777 X0 X1
       have i₂ := eq13101 X1
       grind)
    | exact superpose eq13101 eq1777
    | (have j0 := eq1777 X0 X1
       grind)
    | exact resolve eq1777 eq13101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1777
  have eq14598 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = X0 ∨ (τ X1) = (M.op (τ X1) (τ X1)) ∨ (M.op X0 (τ X1)) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13101 X1
       have i₂ := eq14 (τ X1) X0
       grind)
    | (have i₁ := eq13101 X0
       have i₂ := eq14 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq14 eq13101
    | (have j1 := eq14 (τ X1) (τ X1)
       grind)
    | exact resolve eq13101 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14601 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq13101 X0
       grind)
    | exact superpose eq13101 eq12
    | (have j0 := eq12 (τ X0) X1
       grind)
    | exact resolve eq12 eq13101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13101
  have eq14684 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = X0 ∨ (M.op X0 (τ X1)) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq14598 X0 X1
       have j1 := eq12 (τ X1) X0
       grind)
    | (have r₁ := eq14598 (M.op (τ (M.op X1 X1)) (τ (M.op X1 X1))) X1
       have r₂ := eq12 (τ (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq14598 X0 X1
       have r₂ := eq12 (τ X1) X1
       grind)
    | exact resolve eq14598 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14598
  have eq14793 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = X0 ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13108 X1
       have i₂ := eq14 (σ X1) X0
       grind)
    | (have i₁ := eq13108 X0
       have i₂ := eq14 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq14 eq13108
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq13108 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14836 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq13108 X0
       grind)
    | exact superpose eq13108 eq9
    | exact resolve eq9 eq13108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14872 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq14793 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq14793 (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) X1
       have r₂ := eq12 (σ (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq14793 X0 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq14793 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14793
  have eq15043 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14684 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14684
    | (have j0 := eq14684 X1 (σ X0)
       grind)
    | exact resolve eq14684 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15075 : ∀ X0 X1 : G, (σ X0) = (M.op X1 X1) ∨ (M.op X0 (τ X1)) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 X1)
       have i₂ := eq14684 X0 X1
       grind)
    | (have i₁ := eq11 X0
       have i₂ := eq14684 (τ X0) X1
       grind)
    | exact superpose eq14684 eq11
    | (have j1 := eq14684 X0 X1
       grind)
    | exact resolve eq11 eq14684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14684
  have eq15146 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15043 X0 X1
       have i₂ := eq13108 X0
       grind)
    | exact superpose eq13108 eq15043
    | (have j0 := eq15043 X0 X1
       grind)
    | exact resolve eq15043 eq13108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15043
  have eq15149 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15146 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq15146
    | (have j0 := eq15146 X0 X1
       grind)
    | exact resolve eq15146 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15146
  have eq15331 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq14872 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq14872 (σ X0) X1
       grind)
    | exact superpose eq14872 eq10
    | (have j1 := eq14872 X0 X1
       grind)
    | exact resolve eq10 eq14872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14872
  have eq15583 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (k (τ (σ X1)) X0) = (M.op X0 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13108 X1
       have i₂ := eq15075 X0 (σ X1)
       grind)
    | exact superpose eq15075 eq13108
    | (have j1 := eq15075 X0 (σ X1)
       grind)
    | exact resolve eq13108 eq15075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15075
  have eq15676 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15583 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15583
    | (have j0 := eq15583 X0 X1
       grind)
    | exact resolve eq15583 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15583
  have eq16194 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq15331 (σ X0) X1
       grind)
    | exact superpose eq15331 eq15
    | (have j1 := eq15331 (σ X0) X1
       grind)
    | exact resolve eq15 eq15331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15331
  have eq16288 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16194 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16194
    | (have j0 := eq16194 X0 X1
       grind)
    | exact resolve eq16194 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16194
  have eq17320 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16288 x y
       grind)
    | exact superpose eq16288 eq16
    | (have j1 := eq16288 x y
       grind)
    | exact resolve eq16 eq16288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17556 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17320
       have i₂ := eq15149 y x
       grind)
    | exact superpose eq15149 eq17320
    | (have j1 := eq15149 y x
       grind)
    | exact resolve eq17320 eq15149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17320
  have eq17567 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by grind
  clear eq17556
  have eq17568 : x = (M.op y y) := by grind
  clear eq17567
  have eq18058 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq14836 y X0
       have i₂ := eq17568
       grind)
    | exact superpose eq17568 eq14836
    | exact resolve eq14836 eq17568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14836
  have eq18068 : ∀ X0 : G, (M.op X0 y) = (M.op y (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq17568
       grind)
    | exact superpose eq17568 eq9
    | exact resolve eq9 eq17568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18096 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 x) X0) y) = (M.op y (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18068 (M.op (M.op X1 x) X0)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq18068
    | exact resolve eq18068 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18111 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op x X0) (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 y (M.op x X0)
       have i₂ := eq18068 X0
       grind)
    | exact superpose eq18068 eq9
    | exact resolve eq9 eq18068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18818 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x x))) := by
    first
    | (have i₁ := eq18058 (σ x)
       have i₂ := eq13108 x
       grind)
    | exact superpose eq13108 eq18058
    | exact resolve eq18058 eq13108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21626 : ∀ X0 : G, (M.op y (M.op y (M.op X0 x))) = (M.op (M.op y (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq18096 y (M.op X0 x)
       have i₂ := eq18096 x X0
       grind)
    | exact superpose eq18096 eq18096
    | exact resolve eq18096 eq18096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21644 : ∀ X0 : G, (M.op y (M.op y (M.op X0 x))) = (M.op (M.op X0 y) y) := by
    intro X0
    first
    | (have i₁ := eq21626 X0
       have i₂ := eq18068 X0
       grind)
    | exact superpose eq18068 eq21626
    | exact resolve eq21626 eq18068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18068 eq21626
  have eq21673 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq18111 y X0
       have i₂ := eq17568
       grind)
    | exact superpose eq17568 eq18111
    | exact resolve eq18111 eq17568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21690 : ∀ X0 X1 : G, (M.op X1 (M.op X0 y)) = (M.op (M.op (M.op X1 y) X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 y) X0) x X1
       have i₂ := eq18111 X1 X0
       grind)
    | exact superpose eq18111 eq9
    | exact resolve eq9 eq18111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21787 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op (M.op X0 y) X1)) = (M.op X1 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op x y) (M.op x X0)
       have i₂ := eq21673 X0
       grind)
    | exact superpose eq21673 eq9
    | exact resolve eq9 eq21673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21673
  have eq21788 : ∀ X1 : G, (M.op X1 y) = (M.op X1 (M.op x y)) := by
    intro X1
    first
    | (have i₁ := eq21787 x X1
       have i₂ := eq18111 x X1
       grind)
    | exact superpose eq18111 eq21787
    | exact resolve eq21787 eq18111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21787
  have eq21994 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op X1 (M.op (M.op X0 X1) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op x y) X0 X1
       have i₂ := eq21788 (M.op X0 X1)
       grind)
    | exact superpose eq21788 eq9
    | exact resolve eq9 eq21788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21996 : ∀ X0 : G, (M.op (M.op (M.op X0 x) y) y) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq18096 (M.op x y) X0
       have i₂ := eq21788 (M.op X0 x)
       grind)
    | exact superpose eq21788 eq18096
    | exact resolve eq18096 eq21788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22013 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op (M.op X0 x) y) y) := by
    intro X0
    first
    | (have i₁ := eq21996 X0
       have i₂ := eq9 X0 x y
       grind)
    | exact superpose eq9 eq21996
    | exact resolve eq21996 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21996
  have eq22015 : ∀ X0 : G, (M.op y X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq21994 X0 x
       have i₂ := eq9 y X0 x
       grind)
    | exact superpose eq9 eq21994
    | exact resolve eq21994 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21994
  have eq22043 : ∀ X0 : G, (M.op X0 x) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq22013 X0
       have i₂ := eq18096 y X0
       grind)
    | exact superpose eq18096 eq22013
    | exact resolve eq22013 eq18096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22013
  have eq22118 : ∀ X0 : G, (M.op (M.op X0 x) x) = (M.op (M.op X0 y) y) := by
    intro X0
    first
    | (have i₁ := eq21644 X0
       have i₂ := eq22043 (M.op X0 x)
       grind)
    | exact superpose eq22043 eq21644
    | exact resolve eq21644 eq22043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21644
  have eq22280 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op x x) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq18111 x X0
       have i₂ := eq22015 X0
       grind)
    | exact superpose eq22015 eq18111
    | exact resolve eq18111 eq22015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22015
  have eq22524 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op (M.op (M.op X1 y) X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq22043 (M.op (M.op X1 y) X0)
       have i₂ := eq9 X0 X1 y
       grind)
    | exact superpose eq9 eq22043
    | exact resolve eq22043 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22545 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op X1 (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq22524 X0 X1
       have i₂ := eq21690 X0 X1
       grind)
    | exact superpose eq21690 eq22524
    | exact resolve eq22524 eq21690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21690 eq22524
  have eq22896 : ∀ X0 : G, (M.op y y) = (M.op (M.op x X0) (M.op (M.op X0 x) x)) := by
    intro X0
    first
    | (have i₁ := eq18111 X0 y
       have i₂ := eq22118 X0
       grind)
    | exact superpose eq22118 eq18111
    | exact resolve eq18111 eq22118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22898 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op (M.op (M.op X0 x) x) x) := by
    intro X0
    first
    | (have i₁ := eq18096 y X0
       have i₂ := eq22118 (M.op X0 x)
       grind)
    | exact superpose eq22118 eq18096
    | exact resolve eq18096 eq22118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22904 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op (M.op X0 x) x) x) := by
    intro X0
    first
    | (have i₁ := eq22898 X0
       have i₂ := eq22043 X0
       grind)
    | exact superpose eq22043 eq22898
    | exact resolve eq22898 eq22043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22043 eq22898
  have eq22906 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op (M.op X0 x) x)) := by
    intro X0
    first
    | (have i₁ := eq22896 X0
       have i₂ := eq17568
       grind)
    | exact superpose eq17568 eq22896
    | exact resolve eq22896 eq17568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22896
  have eq23070 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 x) x)) = (M.op x (M.op (M.op X0 x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 x) x) x
       have i₂ := eq22904 X0
       grind)
    | exact superpose eq22904 eq9
    | exact resolve eq9 eq22904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22904
  have eq23071 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op (M.op X0 x) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq23070 X0 X1
       have i₂ := eq9 X1 X0 x
       grind)
    | exact superpose eq9 eq23070
    | exact resolve eq23070 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23070
  have eq23076 : ∀ X0 : G, x = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | (have i₁ := eq22906 X0
       have i₂ := eq23071 X0 (M.op x X0)
       grind)
    | exact superpose eq23071 eq22906
    | exact resolve eq22906 eq23071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22906
  have eq23079 : ∀ X0 X1 : G, x = (M.op (M.op X0 X1) (M.op (M.op X1 x) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23076 (M.op (M.op X1 x) X0)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq23076
    | exact resolve eq23076 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23105 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op X1 (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op x X1) X1
       have i₂ := eq23076 X1
       grind)
    | exact superpose eq23076 eq9
    | exact resolve eq9 eq23076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23076
  have eq23211 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 x) x) X0) = (M.op X1 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X2 x) x) X0 X1
       have i₂ := eq23071 X2 (M.op X0 X1)
       grind)
    | exact superpose eq23071 eq9
    | exact resolve eq9 eq23071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23234 : ∀ X0 X2 : G, (M.op X2 X0) = (M.op (M.op (M.op X2 x) x) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq23211 X0 x X2
       have i₂ := eq9 X2 X0 x
       grind)
    | exact superpose eq9 eq23211
    | exact resolve eq23211 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23211
  have eq23373 : ∀ X0 X1 : G, x = (M.op X0 (M.op (M.op X1 x) X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq23079 X1 X1
       have i₂ := eq15149 X1 X0
       grind)
    | (have i₁ := eq23079 X0 X1
       have i₂ := eq15149 X0 (M.op X0 X1)
       grind)
    | exact superpose eq15149 eq23079
    | (have j1 := eq15149 X1 X0
       grind)
    | exact resolve eq23079 eq15149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15149
  have eq23439 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op (M.op X0 x) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 x) X1) X1 X0
       have i₂ := eq23079 X1 X0
       grind)
    | exact superpose eq23079 eq9
    | exact resolve eq9 eq23079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23952 : ∀ X0 X1 : G, (M.op y X0) = (M.op y (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 y X0 X1
       have i₂ := eq22545 (M.op X0 X1) X1
       grind)
    | (have i₁ := eq9 X1 X1 y
       have i₂ := eq22545 (M.op X1 y) X1
       grind)
    | exact superpose eq22545 eq9
    | exact resolve eq9 eq22545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24014 : ∀ X0 X1 : G, (M.op y (M.op (M.op X0 y) X1)) = (M.op (M.op y (M.op X0 (M.op X1 x))) y) := by
    intro X0 X1
    first
    | (have i₁ := eq18096 (M.op X0 y) X1
       have i₂ := eq22545 X0 (M.op X1 x)
       grind)
    | exact superpose eq22545 eq18096
    | exact resolve eq18096 eq22545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22545
  have eq24035 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op y (M.op X0 (M.op X1 x))) y) := by
    intro X0 X1
    first
    | (have i₁ := eq24014 X0 X1
       have i₂ := eq9 X1 X0 y
       grind)
    | exact superpose eq9 eq24014
    | exact resolve eq24014 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24014
  have eq24216 : ∀ X0 X1 : G, x = (M.op (M.op X1 (M.op X0 x)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23079 X1 (M.op X0 x)
       have i₂ := eq23234 X1 X0
       grind)
    | exact superpose eq23234 eq23079
    | exact resolve eq23079 eq23234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23079
  have eq24217 : ∀ X0 X1 : G, (M.op (M.op X0 X1) y) = (M.op y (M.op X1 (M.op X0 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq18096 X1 (M.op X0 x)
       have i₂ := eq23234 X1 X0
       grind)
    | exact superpose eq23234 eq18096
    | exact resolve eq18096 eq23234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18096
  have eq24218 : ∀ X0 X1 : G, (M.op X1 (M.op X0 x)) = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 x) x
       have i₂ := eq23234 X1 X0
       grind)
    | exact superpose eq23234 eq9
    | exact resolve eq9 eq23234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24358 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq24035 X0 X1
       have i₂ := eq24217 X1 X0
       grind)
    | exact superpose eq24217 eq24035
    | exact resolve eq24035 eq24217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24035
  have eq24428 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) x) x) := by
    intro X0 X1
    first
    | (have i₁ := eq24358 X0 X1
       have i₂ := eq22118 (M.op X1 X0)
       grind)
    | exact superpose eq22118 eq24358
    | exact resolve eq24358 eq22118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22118 eq24358
  have eq24472 : ∀ X0 X1 : G, (M.op (M.op X0 x) x) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23439 (M.op X0 x) X1
       have i₂ := eq23234 X1 X0
       grind)
    | exact superpose eq23234 eq23439
    | exact resolve eq23439 eq23234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24475 : ∀ X0 : G, (M.op x x) = (M.op (M.op X0 y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq23439 x (M.op y X0)
       have i₂ := eq22280 X0
       grind)
    | exact superpose eq22280 eq23439
    | exact resolve eq23439 eq22280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24707 : ∀ X0 : G, (M.op y (M.op x x)) = (M.op y (M.op (M.op X0 y) (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq23952 (M.op x x) (M.op y X0)
       have i₂ := eq22280 X0
       grind)
    | exact superpose eq22280 eq23952
    | exact resolve eq23952 eq22280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22280
  have eq24762 : ∀ X0 : G, (M.op y (M.op x x)) = (M.op (M.op y X0) X0) := by
    intro X0
    first
    | (have i₁ := eq24707 X0
       have i₂ := eq9 (M.op y X0) X0 y
       grind)
    | exact superpose eq9 eq24707
    | exact resolve eq24707 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24707
  have eq24780 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op y X0) X0) := by
    intro X0
    first
    | (have i₁ := eq24762 X0
       have i₂ := eq23105 y x
       grind)
    | (have i₁ := eq24762 X0
       have i₂ := eq23105 x y
       grind)
    | exact superpose eq23105 eq24762
    | exact resolve eq24762 eq23105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24762
  have eq24787 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) X0) := by
    intro X0
    first
    | (have i₁ := eq24780 X0
       have i₂ := eq21788 x
       grind)
    | exact superpose eq21788 eq24780
    | exact resolve eq24780 eq21788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24780
  have eq25276 : ∀ X0 X1 : G, (M.op y X1) = (M.op y (M.op (M.op x (M.op X0 X1)) (M.op X0 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq23952 X1 (M.op X0 x)
       have i₂ := eq24218 X0 X1
       grind)
    | (have i₁ := eq23952 x (M.op X0 X1)
       have i₂ := eq24218 X0 X1
       grind)
    | exact superpose eq24218 eq23952
    | exact resolve eq23952 eq24218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23952 eq24218
  have eq25340 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 (M.op x (M.op X0 X1))) y) := by
    intro X0 X1
    first
    | (have i₁ := eq25276 X0 X1
       have i₂ := eq24217 X0 (M.op x (M.op X0 X1))
       grind)
    | exact superpose eq24217 eq25276
    | exact resolve eq25276 eq24217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24217 eq25276
  have eq25435 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23439 (M.op (M.op X1 X0) x) X1
       have i₂ := eq24428 X0 X1
       grind)
    | exact superpose eq24428 eq23439
    | exact resolve eq23439 eq24428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23439 eq24428
  have eq25746 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24472 X0 X2
       have i₂ := eq24472 X0 X1
       grind)
    | (have i₁ := eq24472 X0 X1
       have i₂ := eq24472 X0 x
       grind)
    | exact superpose eq24472 eq24472
    | exact resolve eq24472 eq24472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25812 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23071 X0 X2
       have i₂ := eq24472 X0 X1
       grind)
    | (have i₁ := eq23071 X0 X1
       have i₂ := eq24472 X0 x
       grind)
    | exact superpose eq24472 eq23071
    | exact resolve eq23071 eq24472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23071
  have eq25844 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op X2 (M.op (M.op (M.op X0 x) x) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X0 X2) X2
       have i₂ := eq24472 X0 X2
       grind)
    | (have i₁ := eq9 X0 (M.op X0 x) x
       have i₂ := eq24472 X0 X1
       grind)
    | exact superpose eq24472 eq9
    | exact resolve eq9 eq24472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25858 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 x) x) (M.op X1 (M.op X0 (M.op X1 x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq24216 X1 (M.op X0 (M.op X1 x))
       have i₂ := eq24472 X0 (M.op X1 x)
       grind)
    | exact superpose eq24472 eq24216
    | exact resolve eq24216 eq24472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24216 eq24472
  have eq25865 : ∀ X0 X1 : G, x = (M.op X0 (M.op X1 (M.op X0 (M.op X1 x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25858 X0 X1
       have i₂ := eq23234 (M.op X1 (M.op X0 (M.op X1 x))) X0
       grind)
    | (have i₁ := eq25858 X0 X1
       have i₂ := eq23234 (M.op X1 (M.op X0 (M.op X1 x))) (M.op (M.op X0 x) x)
       grind)
    | exact superpose eq23234 eq25858
    | exact resolve eq25858 eq23234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25858
  have eq25874 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X1 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25844 X0 X2 X1
       have i₂ := eq23234 X2 X0
       grind)
    | (have i₁ := eq25844 X0 X0 X2
       have i₂ := eq23234 X0 (M.op (M.op X0 x) x)
       grind)
    | exact superpose eq23234 eq25844
    | exact resolve eq25844 eq23234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23234 eq25844
  have eq26073 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op (M.op x X0) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq18111 X0 (M.op y X0)
       have i₂ := eq24475 X0
       grind)
    | exact superpose eq24475 eq18111
    | exact resolve eq18111 eq24475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18111 eq24475
  have eq26198 : ∀ X0 : G, (M.op x (M.op x (M.op x X0))) = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq26073 X0
       have i₂ := eq23105 (M.op x X0) x
       grind)
    | (have i₁ := eq26073 X0
       have i₂ := eq23105 x (M.op x X0)
       grind)
    | exact superpose eq23105 eq26073
    | exact resolve eq26073 eq23105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26073
  have eq26605 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ (M.op X0 X0)) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25435 (σ X0) (σ X0) x
       have i₂ := eq13108 X0
       grind)
    | exact superpose eq13108 eq25435
    | exact resolve eq25435 eq13108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28007 : x = (M.op (σ x) (M.op (M.op (σ y) x) (σ y))) := by
    first
    | (have i₁ := eq25865 (σ x) (σ y)
       have i₂ := eq18058 (M.op (σ y) x)
       grind)
    | exact superpose eq18058 eq25865
    | exact resolve eq25865 eq18058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25865
  have eq28341 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = (M.op (σ X0) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25874 (σ X0) X1 (σ X0)
       have i₂ := eq13108 X0
       grind)
    | exact superpose eq13108 eq25874
    | exact resolve eq25874 eq13108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28591 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq18058 X0
       have i₂ := eq25874 (σ x) X0 (σ y)
       grind)
    | (have i₁ := eq18058 X0
       have i₂ := eq25874 (σ x) (σ y) X0
       grind)
    | exact superpose eq25874 eq18058
    | exact resolve eq18058 eq25874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29995 : ∀ X0 : G, (M.op x (M.op (M.op (σ y) x) (σ y))) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq25746 (σ x) X0 (M.op (M.op (σ y) x) (σ y))
       have i₂ := eq28007
       grind)
    | exact superpose eq28007 eq25746
    | exact resolve eq25746 eq28007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28007
  have eq30002 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq29995 X0
       have i₂ := eq9 (σ y) (σ y) x
       grind)
    | exact superpose eq9 eq29995
    | exact resolve eq29995 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29995
  have eq30010 : ∀ X0 : G, (σ (M.op y y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq30002 X0
       have i₂ := eq13108 y
       grind)
    | exact superpose eq13108 eq30002
    | exact resolve eq30002 eq13108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30002
  have eq30016 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq30010 X0
       have i₂ := eq17568
       grind)
    | exact superpose eq17568 eq30010
    | exact resolve eq30010 eq17568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30010
  have eq30845 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op X1 (M.op (M.op X0 X1) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (σ x) (σ y)) X0 X1
       have i₂ := eq28591 (M.op X0 X1)
       grind)
    | exact superpose eq28591 eq9
    | exact resolve eq9 eq28591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30895 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq30845 X0 x
       have i₂ := eq9 (σ y) X0 x
       grind)
    | exact superpose eq9 eq30845
    | exact resolve eq30845 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30845
  have eq31529 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq25435 (σ x) (σ y) X0
       have i₂ := eq30895 X0
       grind)
    | exact superpose eq30895 eq25435
    | exact resolve eq25435 eq30895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30895
  have eq33125 : (M.op (σ x) (σ y)) = (σ (k (M.op x x) y)) ∨ y = (M.op (M.op x x) (M.op x x)) := by
    first
    | (have i₁ := eq16288 y (M.op x x)
       have i₂ := eq18818
       grind)
    | exact superpose eq18818 eq16288
    | (have j0 := eq16288 y (M.op x x)
       grind)
    | exact resolve eq16288 eq18818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16288
  have eq33138 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (σ (M.op x x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq25874 (σ y) X0 (σ (M.op x x))
       have i₂ := eq18818
       grind)
    | exact superpose eq18818 eq25874
    | exact resolve eq25874 eq18818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18818
  have eq33139 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ (M.op x x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq33138 X0
       have i₂ := eq28591 X0
       grind)
    | exact superpose eq28591 eq33138
    | exact resolve eq33138 eq28591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33138
  have eq33151 : y = (M.op x (M.op x (M.op x x))) ∨ (M.op (σ x) (σ y)) = (σ (k (M.op x x) y)) := by
    first
    | (have i₁ := eq33125
       have i₂ := eq23105 (M.op x x) x
       grind)
    | (have i₁ := eq33125
       have i₂ := eq23105 x (M.op x x)
       grind)
    | exact superpose eq23105 eq33125
    | exact resolve eq33125 eq23105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33125
  have eq33162 : y = (M.op (M.op y x) y) ∨ (M.op (σ x) (σ y)) = (σ (k (M.op x x) y)) := by
    first
    | (have i₁ := eq33151
       have i₂ := eq26198 x
       grind)
    | exact superpose eq26198 eq33151
    | exact resolve eq33151 eq26198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26198 eq33151
  have eq37668 : ∀ X0 X1 : G, (M.op (M.op y X0) y) = (M.op X1 (M.op x (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq25435 X1 (M.op x (M.op X1 X0)) y
       have i₂ := eq25340 X1 X0
       grind)
    | exact superpose eq25340 eq25435
    | exact resolve eq25435 eq25340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25340 eq25435
  have eq39175 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ X0) X2) X2) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26605 X0 X1
       have i₂ := eq15676 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq26605 X1 X1
       have i₂ := eq15676 X0 X1
       grind)
    | exact superpose eq15676 eq26605
    | (have j1 := eq15676 X0 X1
       grind)
    | exact resolve eq26605 eq15676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60646 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ y)) = (M.op (σ y) (M.op X0 (σ (M.op x x)))) := by
    intro X0
    first
    | (have i₁ := eq18058 (M.op (σ x) X0)
       have i₂ := eq28341 x X0
       grind)
    | exact superpose eq28341 eq18058
    | exact resolve eq18058 eq28341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18058
  have eq62679 : ∀ X0 : G, (σ (M.op x x)) = (M.op (M.op X0 (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq26605 x (M.op (σ y) X0)
       have i₂ := eq33139 X0
       grind)
    | exact superpose eq33139 eq26605
    | exact resolve eq26605 eq33139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26605
  have eq62681 : ∀ X0 : G, (M.op (σ (M.op x x)) (M.op X0 (σ y))) = (M.op (M.op (σ y) X0) (σ (M.op (M.op x x) (M.op x x)))) := by
    intro X0
    first
    | (have i₁ := eq28341 (M.op x x) (M.op (σ y) X0)
       have i₂ := eq33139 X0
       grind)
    | exact superpose eq33139 eq28341
    | exact resolve eq28341 eq33139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62754 : ∀ X0 : G, (M.op (σ (M.op x x)) (M.op X0 (σ y))) = (M.op (M.op (σ y) X0) (σ (M.op x (M.op x (M.op x x))))) := by
    intro X0
    first
    | (have i₁ := eq62681 X0
       have i₂ := eq23105 (M.op x x) x
       grind)
    | (have i₁ := eq62681 X0
       have i₂ := eq23105 x (M.op x x)
       grind)
    | exact superpose eq23105 eq62681
    | exact resolve eq62681 eq23105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62681
  have eq62757 : ∀ X0 : G, (σ (M.op x x)) = (M.op X0 (M.op (σ y) (M.op X0 (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq62679 X0
       have i₂ := eq25874 (σ y) X0 (M.op X0 (σ y))
       grind)
    | (have i₁ := eq62679 X0
       have i₂ := eq25874 (σ y) (M.op X0 (σ y)) X0
       grind)
    | exact superpose eq25874 eq62679
    | exact resolve eq62679 eq25874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62679
  have eq62816 : ∀ X0 : G, (M.op (σ (M.op x x)) (M.op X0 (σ y))) = (M.op (M.op (σ y) X0) (σ (M.op (M.op y x) y))) := by
    intro X0
    first
    | (have i₁ := eq62754 X0
       have i₂ := eq37668 x x
       grind)
    | exact superpose eq37668 eq62754
    | exact resolve eq62754 eq37668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62754
  have eq62844 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ (M.op x x)))) = (M.op (M.op (σ y) X0) (σ (M.op (M.op y x) y))) := by
    intro X0
    first
    | (have i₁ := eq62816 X0
       have i₂ := eq25874 X0 (σ y) (σ (M.op x x))
       grind)
    | (have i₁ := eq62816 X0
       have i₂ := eq25874 X0 (σ (M.op x x)) (σ y)
       grind)
    | exact superpose eq25874 eq62816
    | exact resolve eq62816 eq25874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25874 eq62816
  have eq62858 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ y)) = (M.op (M.op (σ y) X0) (σ (M.op (M.op y x) y))) := by
    intro X0
    first
    | (have i₁ := eq62844 X0
       have i₂ := eq60646 X0
       grind)
    | exact superpose eq60646 eq62844
    | exact resolve eq62844 eq60646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60646 eq62844
  have eq68477 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (M.op (σ y) (M.op (σ y) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq33139 (M.op (σ y) (M.op (σ y) (σ y)))
       have i₂ := eq62757 (σ y)
       grind)
    | exact superpose eq62757 eq33139
    | exact resolve eq33139 eq62757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33139 eq62757
  have eq68546 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (M.op (σ y) (σ (M.op y y))) (σ y)) := by
    first
    | (have i₁ := eq68477
       have i₂ := eq28341 y (σ y)
       grind)
    | exact superpose eq28341 eq68477
    | exact resolve eq68477 eq28341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28341 eq68477
  have eq68640 : (M.op (M.op (σ y) (σ x)) (σ y)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq68546
       have i₂ := eq17568
       grind)
    | exact superpose eq17568 eq68546
    | exact resolve eq68546 eq17568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68546
  have eq68693 : (M.op (M.op (σ y) (σ x)) (σ y)) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq68640
       have i₂ := eq13108 (M.op x x)
       grind)
    | exact superpose eq13108 eq68640
    | exact resolve eq68640 eq13108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68640
  have eq68732 : (M.op (M.op (σ y) (σ x)) (σ y)) = (σ (M.op x (M.op x (M.op x x)))) := by
    first
    | (have i₁ := eq68693
       have i₂ := eq23105 (M.op x x) x
       grind)
    | (have i₁ := eq68693
       have i₂ := eq23105 x (M.op x x)
       grind)
    | exact superpose eq23105 eq68693
    | exact resolve eq68693 eq23105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68693
  have eq68757 : (M.op (M.op (σ y) (σ x)) (σ y)) = (σ (M.op (M.op y x) y)) := by
    first
    | (have i₁ := eq68732
       have i₂ := eq37668 x x
       grind)
    | exact superpose eq37668 eq68732
    | exact resolve eq68732 eq37668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37668 eq68732
  have eq239612 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ (M.op (M.op y x) y))) := by
    first
    | (have i₁ := eq9 (σ y) (σ y) (σ x)
       have i₂ := eq68757
       grind)
    | exact superpose eq68757 eq9
    | exact resolve eq9 eq68757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239759 : (σ (M.op y y)) = (M.op (σ x) (σ (M.op (M.op y x) y))) := by
    first
    | (have i₁ := eq239612
       have i₂ := eq13108 y
       grind)
    | exact superpose eq13108 eq239612
    | exact resolve eq239612 eq13108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239612
  have eq239798 : (σ x) = (M.op (σ x) (σ (M.op (M.op y x) y))) := by
    first
    | (have i₁ := eq239759
       have i₂ := eq17568
       grind)
    | exact superpose eq17568 eq239759
    | exact resolve eq239759 eq17568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239759
  have eq271590 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op X1 (τ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 (τ X0))
       have i₂ := eq13162 X1 X0
       grind)
    | exact superpose eq13162 eq10
    | (have j1 := eq13162 X1 X0
       grind)
    | exact resolve eq10 eq13162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13162
  have eq271848 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq271590 X0 X1
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq271590
    | (have j0 := eq271590 X0 X1
       grind)
    | exact resolve eq271590 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271590
  have eq272040 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq271848 X0 X1
       have j1 := eq14601 X0 X1
       grind)
    | (have r₁ := eq271848 X0 X1
       have r₂ := eq14601 X0 X1
       grind)
    | exact resolve eq271848 eq14601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14601 eq271848
  have eq272410 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq272040 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq272040
    | (have j0 := eq272040 (σ X0) X1
       grind)
    | exact resolve eq272040 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272040
  have eq272610 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq272410 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq272410
    | (have j0 := eq272410 X0 X1
       grind)
    | exact resolve eq272410 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272410
  have eq272872 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq272610 X0 X1
       grind)
    | exact superpose eq272610 eq10
    | (have j1 := eq272610 X0 X1
       grind)
    | exact resolve eq10 eq272610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272610
  have eq272952 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq272872 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq272872
    | (have j0 := eq272872 X0 X1
       grind)
    | exact resolve eq272872 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272872
  have eq273200 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq272952 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272952
  have eq298836 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op x (M.op (M.op X2 x) X2)) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25746 X0 X1 (M.op (M.op X2 x) X2)
       have i₂ := eq23373 X0 X2
       grind)
    | exact superpose eq23373 eq25746
    | (have j1 := eq23373 X0 X2
       grind)
    | exact resolve eq25746 eq23373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25746
  have eq299006 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op X0 x) X0)) ∨ (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq24787 (M.op (M.op X0 x) X0)
       have i₂ := eq23373 y X0
       grind)
    | exact superpose eq23373 eq24787
    | (have j1 := eq23373 y X0
       grind)
    | exact resolve eq24787 eq23373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23373 eq24787
  have eq299052 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) ∨ (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq299006 X0
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq299006
    | (have j0 := eq299006 X0
       grind)
    | exact resolve eq299006 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299006
  have eq299173 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 X1) X1) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq298836 X0 X1 X2
       have i₂ := eq9 X2 X2 x
       grind)
    | exact superpose eq9 eq298836
    | (have j0 := eq298836 X0 X1 X2
       grind)
    | exact resolve eq298836 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298836
  have eq347964 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) ≠ X2 ∨ (k X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq273200 X2 X2
       have i₂ := eq299173 X0 X1 X2
       grind)
    | exact superpose eq299173 eq273200
    | (have j0 := eq273200 X2 X2
       have j1 := eq299173 X0 X1 X2
       grind)
    | (have r₁ := eq273200 (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)
       have r₂ := eq299173 X0 X1 (M.op (M.op X0 X1) X1)
       grind)
    | (have r₁ := eq273200 (M.op X2 X2) (M.op X0 (M.op X2 X2))
       have r₂ := eq299173 X0 (M.op X2 X2) X2
       grind)
    | exact resolve eq273200 eq299173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273200 eq299173
  have eq348328 : ∀ X0 X1 X2 : G, (M.op X2 X2) = X2 ∨ (M.op (M.op X0 X1) X1) ≠ X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq347964 X0 X1 X2
       have i₂ := eq11155 X2
       grind)
    | exact superpose eq11155 eq347964
    | (have j0 := eq347964 X0 X1 X2
       grind)
    | exact resolve eq347964 eq11155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11155 eq347964
  have eq348495 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) ≠ X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq348328 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq348328 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq348328 X0 X0 (k X0 (M.op X0 X0))
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq348328 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348328
  have eq348874 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X1)) = (k (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq348495 X0 X1 (M.op (M.op X0 X1) X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348495
  have eq348875 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq348874 X0 X1
       have i₂ := eq25812 X0 X1 X0
       grind)
    | exact superpose eq25812 eq348874
    | exact resolve eq348874 eq25812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25812 eq348874
  have eq349451 : (M.op (σ y) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq348875 (σ y) x
       have i₂ := eq31529 x
       grind)
    | exact superpose eq31529 eq348875
    | exact resolve eq348875 eq31529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348875
  have eq349740 : (σ (M.op y y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq349451
       have i₂ := eq13108 y
       grind)
    | exact superpose eq13108 eq349451
    | exact resolve eq349451 eq13108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13108 eq349451
  have eq349936 : (σ x) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq349740
       have i₂ := eq17568
       grind)
    | exact superpose eq17568 eq349740
    | exact resolve eq349740 eq17568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17568 eq349740
  have eq350356 : (τ (σ x)) = (k (τ (M.op (σ x) (σ y))) y) := by
    first
    | (have i₁ := eq30 (M.op (σ x) (σ y)) y
       have i₂ := eq349936
       grind)
    | exact superpose eq349936 eq30
    | exact resolve eq30 eq349936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq349936
  have eq350383 : x = (k (τ (M.op (σ x) (σ y))) y) := by
    first
    | (have i₁ := eq350356
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq350356
    | exact resolve eq350356 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350356
  have eq360940 : ∀ X1 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y X1) = (k X1 y) := by
    intro X1
    first
    | (have i₁ := eq31529 x
       have i₂ := eq39175 y X1 x
       grind)
    | exact superpose eq39175 eq31529
    | (have j1 := eq39175 y X1 x
       grind)
    | exact resolve eq31529 eq39175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31529 eq39175
  have eq361297 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq360940 X0
       grind)
    | exact superpose eq360940 eq16
    | (have j1 := eq360940 X0
       grind)
    | exact resolve eq16 eq360940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360940
  have eq361418 : ∀ X0 X1 : G, (σ y) ≠ (σ (M.op X0 X0)) ∨ (M.op y X1) = (k X1 y) ∨ (k X0 y) = (M.op y X0) := by
    intro X0 X1
    first
    | (have i₁ := eq361297 X1
       have i₂ := eq299052 X0
       grind)
    | exact superpose eq299052 eq361297
    | (have j0 := eq361297 X1
       have j1 := eq299052 X1
       grind)
    | exact resolve eq361297 eq299052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299052 eq361297
  have eq361424 : ∀ X0 X1 : G, (M.op y X1) = (k X1 y) ∨ (k X0 y) = (M.op y X0) := by
    intro X0 X1
    first
    | (have j0 := eq361418 X1 X1
       have j1 := eq15676 y X1
       grind)
    | (have r₁ := eq361418 X1 X1
       have r₂ := eq15676 y X1
       grind)
    | exact resolve eq361418 eq15676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15676 eq361418
  have eq361538 : ∀ X0 : G, (M.op y X0) ≠ (M.op y X0) ∨ (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq361424 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361424
  have eq361539 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq361538 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361538
  have eq361886 : (M.op (σ x) (σ y)) = (σ (M.op y (M.op x x))) ∨ y = (M.op (M.op y x) y) := by
    first
    | (have i₁ := eq33162
       have i₂ := eq361539 (M.op x x)
       grind)
    | exact superpose eq361539 eq33162
    | exact resolve eq33162 eq361539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33162
  have eq362062 : x = (M.op y (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq350383
       have i₂ := eq361539 (τ (M.op (σ x) (σ y)))
       grind)
    | exact superpose eq361539 eq350383
    | exact resolve eq350383 eq361539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350383 eq361539
  have eq362118 : (M.op (σ x) (σ y)) = (σ (M.op x (M.op x y))) ∨ y = (M.op (M.op y x) y) := by
    first
    | (have i₁ := eq361886
       have i₂ := eq23105 y x
       grind)
    | (have i₁ := eq361886
       have i₂ := eq23105 x y
       grind)
    | exact superpose eq23105 eq361886
    | exact resolve eq361886 eq23105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23105 eq361886
  have eq362178 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op (M.op y x) y) := by
    first
    | (have i₁ := eq362118
       have i₂ := eq21788 x
       grind)
    | exact superpose eq21788 eq362118
    | exact resolve eq362118 eq21788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21788 eq362118
  have eq362190 : y = (M.op (M.op y x) y) := by
    first
    | (have r₁ := eq362178
       have r₂ := eq16
       grind)
    | exact resolve eq362178 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362178
  have eq362218 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq62858 X0
       have i₂ := eq362190
       grind)
    | exact superpose eq362190 eq62858
    | exact resolve eq62858 eq362190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62858
  have eq362226 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq68757
       have i₂ := eq362190
       grind)
    | exact superpose eq362190 eq68757
    | exact resolve eq68757 eq362190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68757
  have eq362347 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq239798
       have i₂ := eq362190
       grind)
    | exact superpose eq362190 eq239798
    | exact resolve eq239798 eq362190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239798
  have eq362603 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq362347
       grind)
    | exact superpose eq362347 eq16
    | exact resolve eq16 eq362347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362614 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq28591 X0
       have i₂ := eq362347
       grind)
    | exact superpose eq362347 eq28591
    | exact resolve eq28591 eq362347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28591
  have eq362947 : x = (M.op y (τ (σ x))) := by
    first
    | (have i₁ := eq362062
       have i₂ := eq362347
       grind)
    | exact superpose eq362347 eq362062
    | exact resolve eq362062 eq362347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362062 eq362347
  have eq363392 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq362226
       have i₂ := eq362218 (σ x)
       grind)
    | exact superpose eq362218 eq362226
    | exact resolve eq362226 eq362218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362218 eq362226
  have eq363589 : x = (M.op y x) := by
    first
    | (have i₁ := eq362947
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq362947
    | exact resolve eq362947 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362947
  have eq368387 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq363392
       have i₂ := eq362614 (M.op (σ x) (σ x))
       grind)
    | exact superpose eq362614 eq363392
    | exact resolve eq363392 eq362614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362614 eq363392
  have eq369420 : y = (M.op x y) := by
    first
    | (have i₁ := eq362190
       have i₂ := eq363589
       grind)
    | exact superpose eq363589 eq362190
    | exact resolve eq362190 eq363589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362190 eq363589
  have eq371554 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq368387
       have i₂ := eq30016 (σ x)
       grind)
    | exact superpose eq30016 eq368387
    | exact resolve eq368387 eq30016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30016 eq368387
  have eq373252 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq362603
       have i₂ := eq369420
       grind)
    | exact superpose eq369420 eq362603
    | exact resolve eq362603 eq369420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362603 eq369420
  have eq381255 : False := by grind
  exact eq381255

/-- `Equation3617`: `x ◇ y = z ◇ ((z ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pyx_y_pyx_Equation3617 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3617 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3617.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X2 X0) X1)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  clear eq18
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X2 (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X2 X0) X1) X3 X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op (M.op X3 X2) X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op (M.op X3 X2) X0) X1) X3
       have i₂ := eq9 X0 X1 (M.op X3 X2)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X1)) = (M.op X2 (M.op X3 (M.op (M.op X2 X0) X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X0 X1 X2 X3
       have i₂ := eq24 X2 X0 X3 X1
       grind)
    | exact superpose eq24 eq25
    | exact resolve eq25 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq37 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X2 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq23
    | exact resolve eq23 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq23
  have eq55 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X2 X0) X1) ∨ (k X2 (M.op (M.op X2 X0) X1)) = (M.op (M.op (M.op X2 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op (M.op X2 X0) X1)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X2 (M.op (M.op X2 X0) X1)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X2 X0) X1) ∨ (k X2 (M.op (M.op X2 X0) X1)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X0 X1 X2
       have i₂ := eq24 X0 X1 X2 X2
       grind)
    | exact superpose eq24 eq55
    | (have j0 := eq55 X0 X1 X2
       grind)
    | exact resolve eq55 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq102 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op X0 X2)) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 (M.op X2 X0) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op X0 X2)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq102 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq102 X0 X0 X2
       have r₂ := eq12 X0 (M.op X0 X2)
       grind)
    | (have r₁ := eq102 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq102 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq194 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op (M.op X3 X1) X2)) X4) = (M.op X3 (M.op (M.op X0 (M.op X1 X2)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 (M.op (M.op X3 X1) X2)) X4 X3
       have i₂ := eq26 X1 X2 X3 X0
       grind)
    | exact superpose eq26 eq9
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq327 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X0 X1) X2)) = (M.op X3 (M.op X1 X2)) ∨ (M.op X0 X3) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq26 X1 X2 X0 X3
       have i₂ := eq118 X3 X0 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq118 eq26
    | (have j1 := eq118 X3 X0 X2
       grind)
    | exact resolve eq26 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq361 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X3 (M.op X1 X2)) ∨ (M.op X0 X3) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq327 X0 X1 X2 X3
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq327
    | (have j0 := eq327 X0 X1 X2 X3
       grind)
    | exact resolve eq327 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq1164 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X2 (M.op (M.op (M.op X3 X2) X0) X1)) ∨ (k X3 (M.op X0 X1)) = (M.op X3 (M.op (M.op X2 (M.op (M.op (M.op X3 X2) X0) X1)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X0 (M.op (M.op (M.op X2 X0) X0) X1) X2
       have i₂ := eq9 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq9 eq56
    | exact resolve eq56 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1177 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X2 (M.op X3 (M.op (M.op X2 X0) X1))) ∨ (k X3 (M.op X0 X1)) = (M.op X3 (M.op (M.op X2 (M.op (M.op (M.op X3 X2) X0) X1)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1164 X0 X1 X2 X3
       have i₂ := eq24 X2 X0 X3 X1
       grind)
    | exact superpose eq24 eq1164
    | (have j0 := eq1164 X0 X1 X2 X3
       grind)
    | exact resolve eq1164 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1164
  have eq1191 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X3 (M.op X0 X1)) ∨ (k X3 (M.op X0 X1)) = (M.op X3 (M.op (M.op X2 (M.op (M.op (M.op X3 X2) X0) X1)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1177 X0 X1 X2 X3
       have i₂ := eq26 X0 X1 X2 X3
       grind)
    | exact superpose eq26 eq1177
    | (have j0 := eq1177 X0 X1 X2 X3
       grind)
    | exact resolve eq1177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1177
  have eq1202 : ∀ X0 X1 X2 X3 : G, (k X3 (M.op X0 X1)) = (M.op X3 (M.op (M.op X3 X2) (M.op (M.op X2 (M.op X0 X1)) X3))) ∨ (M.op X0 X1) ≠ (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1191 X0 X1 X2 X3
       have i₂ := eq194 X2 X0 X1 (M.op X3 X2) X3
       grind)
    | exact superpose eq194 eq1191
    | (have j0 := eq1191 X0 X1 X2 X3
       grind)
    | exact resolve eq1191 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq1191
  have eq1209 : ∀ X0 X1 X2 X3 : G, (k X3 (M.op X0 X1)) = (M.op X2 (M.op (M.op X2 (M.op X0 X1)) X3)) ∨ (M.op X0 X1) ≠ (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1202 X0 X1 X2 X3
       have i₂ := eq9 X2 (M.op (M.op X2 (M.op X0 X1)) X3) X3
       grind)
    | exact superpose eq9 eq1202
    | (have j0 := eq1202 X0 X1 X2 X3
       grind)
    | exact resolve eq1202 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202
  have eq1214 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X3) = (k X3 (M.op X0 X1)) ∨ (M.op X0 X1) ≠ (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1209 X0 X1 x X3
       have i₂ := eq9 (M.op X0 X1) X3 x
       grind)
    | exact superpose eq9 eq1209
    | (have j0 := eq1209 X0 X1 x X3
       grind)
    | exact resolve eq1209 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq1218 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X3) = (k X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have j0 := eq1214 X0 X1 X3
       have j1 := eq361 (M.op X0 X1) X1 x X3
       grind)
    | (have r₁ := eq1214 X1 x X3
       have r₂ := eq361 X0 X1 x X3
       grind)
    | exact resolve eq1214 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361 eq1214
  have eq1323 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1218 X1 X1 x
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq1218 X0 X1 x
       have i₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact superpose eq14 eq1218
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq1218 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1332 : ∀ X0 X1 X2 : G, (k X2 (τ (M.op X0 X1))) = (τ (M.op (M.op X0 X1) (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 X2 (M.op X0 X1)
       have i₂ := eq1218 X0 X1 (σ X2)
       grind)
    | exact superpose eq1218 eq32
    | exact resolve eq32 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq1340 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1323 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq1323 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1323 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323
  have eq1698 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1340 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340
  have eq1699 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1698 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1698
  have eq1733 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1699 (σ X0)
       grind)
    | exact superpose eq1699 eq15
    | exact resolve eq15 eq1699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1735 : ∀ X0 X1 : G, (τ (k X1 (M.op (σ X0) (σ X0)))) = (k (τ X1) (k X0 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X0) X1
       have i₂ := eq1699 (σ X0)
       grind)
    | exact superpose eq1699 eq37
    | exact resolve eq37 eq1699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq1750 : ∀ X0 X1 : G, (τ (k X1 (M.op (σ X0) (σ X0)))) = (k (τ X1) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1735 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1735
    | exact resolve eq1735 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1735
  have eq1752 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1733 X0
       have i₂ := eq1699 X0
       grind)
    | exact superpose eq1699 eq1733
    | exact resolve eq1733 eq1699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1733
  have eq1775 : ∀ X0 X1 : G, (τ (k X1 (M.op (σ X0) (σ X0)))) = (k (τ X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1750 X0 X1
       have i₂ := eq1699 X0
       grind)
    | exact superpose eq1699 eq1750
    | exact resolve eq1750 eq1699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1699 eq1750
  have eq1852 : ∀ X0 X1 : G, (τ (k X1 (M.op (σ X0) (σ X0)))) = (M.op (M.op X0 X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1775 X0 X1
       have i₂ := eq1218 X0 X0 (τ X1)
       grind)
    | exact superpose eq1218 eq1775
    | exact resolve eq1775 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775
  have eq1880 : ∀ X0 X1 : G, (τ (M.op (M.op (σ X0) (σ X0)) X1)) = (M.op (M.op X0 X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1852 X0 X1
       have i₂ := eq1218 (σ X0) (σ X0) X1
       grind)
    | exact superpose eq1218 eq1852
    | exact resolve eq1852 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1852
  have eq1892 : ∀ X0 X1 : G, (τ (M.op (σ (M.op X0 X0)) X1)) = (M.op (M.op X0 X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1880 X0 X1
       have i₂ := eq1752 X0
       grind)
    | exact superpose eq1752 eq1880
    | exact resolve eq1880 eq1752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1880
  have eq1958 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (M.op (σ X0) X1) X2)) = (M.op (M.op (σ (M.op X0 X0)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (σ X0) X1 (σ X0) X2
       have i₂ := eq1752 X0
       grind)
    | exact superpose eq1752 eq24
    | exact resolve eq24 eq1752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1752
  have eq1979 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (σ (M.op X0 X0)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1958 X0 X1 X2
       have i₂ := eq9 X1 X2 (σ X0)
       grind)
    | exact superpose eq9 eq1958
    | exact resolve eq1958 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1958
  have eq2417 : ∀ X0 X1 X2 : G, (τ (M.op X0 (σ X1))) = (k X1 (τ (M.op (σ (M.op X2 X2)) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1332 (σ (M.op X2 X2)) X0 X1
       have i₂ := eq1979 X2 X0 (σ X1)
       grind)
    | exact superpose eq1979 eq1332
    | exact resolve eq1332 eq1979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332 eq1979
  have eq2461 : ∀ X0 X1 X2 : G, (τ (M.op X0 (σ X1))) = (k X1 (M.op (M.op X2 X2) (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2417 X0 X1 X2
       have i₂ := eq1892 X2 X0
       grind)
    | exact superpose eq1892 eq2417
    | exact resolve eq2417 eq1892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1892 eq2417
  have eq2493 : ∀ X0 X1 X2 : G, (τ (M.op X0 (σ X1))) = (M.op (M.op (M.op X2 X2) (τ X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2461 X0 X1 X2
       have i₂ := eq1218 (M.op X2 X2) (τ X0) X1
       grind)
    | exact superpose eq1218 eq2461
    | exact resolve eq2461 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218 eq2461
  have eq2505 : ∀ X0 X1 X2 : G, (τ (M.op X0 (σ X1))) = (M.op X2 (M.op (M.op X2 (τ X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2493 X0 X1 X2
       have i₂ := eq24 X2 (τ X0) X2 X1
       grind)
    | exact superpose eq24 eq2493
    | exact resolve eq2493 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2493
  have eq2507 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2505 X0 X1 x
       have i₂ := eq9 (τ X0) X1 x
       grind)
    | exact superpose eq9 eq2505
    | exact resolve eq2505 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2505
  have eq2567 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 (σ X1))
       have i₂ := eq2507 X0 X1
       grind)
    | exact superpose eq2507 eq11
    | exact resolve eq11 eq2507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2507
  have eq2873 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2567 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2567
    | exact resolve eq2567 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2567
  have eq3009 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2873 x y
       grind)
    | exact superpose eq2873 eq16
    | (have r₁ := eq16
       have r₂ := eq2873 x y
       grind)
    | exact resolve eq16 eq2873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2873
  have eq3010 : False := by grind
  exact eq3010

/-- `Equation3735`: `x ◇ y = (x ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_x_pxy_pxx_pyx_Equation3735 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3735 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3735.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    grind
  have eq18 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    first
    | (have j0 := eq17 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq19 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq10 X0
       grind)
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    grind
  have eq21 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    first
    | (have j0 := eq20 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq22 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0
       grind)
    | exact resolve eq11 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : (M.op x y) = (M.op x y) := by grind
  have eq24 : (M.op x y) = (M.op x y) := by grind
  clear eq23
  have eq25 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq26 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq25
  have eq27 : (σ x) = (σ x) := by grind
  have eq28 : (σ x) = (σ x) := by grind
  clear eq27
  have eq29 : (σ y) = (σ y) := by grind
  have eq30 : (σ y) = (σ y) := by grind
  clear eq29
  have eq31 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq32 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq31
  have eq33 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq34 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq19 eq18
    | (have j1 := eq19 X0
       grind)
    | exact resolve eq18 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq19
  have eq35 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq22 eq21
    | (have j1 := eq22 X0
       grind)
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq22
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq34 x
       have i₂ := eq28
       grind)
    | exact superpose eq28 eq34
    | (have j0 := eq34 x
       grind)
    | exact resolve eq34 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq40 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq34 y
       have i₂ := eq30
       grind)
    | exact superpose eq30 eq34
    | (have j0 := eq34 y
       grind)
    | exact resolve eq34 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq41 : (M.op x y) = (M.op (τ (σ x)) y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq38
       grind)
    | exact superpose eq38 eq24
    | exact resolve eq24 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq38
  have eq42 : (M.op x y) = (M.op (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq41
       have i₂ := eq40
       grind)
    | exact superpose eq40 eq41
    | exact resolve eq41 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq41
  have eq46 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq34
    | exact resolve eq34 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq47 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq46 (τ X0) X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq46
    | exact resolve eq46 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq26 eq46
    | (have j0 := eq46 (M.op x y) X0
       grind)
    | exact resolve eq46 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X0 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X2) X3 (M.op X1 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (M.op (τ (σ x)) X0) = (M.op (M.op x y) (M.op X0 (τ (σ x)))) := by
    intro X0
    first
    | exact superpose eq42 eq9
    | exact resolve eq9 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq32 eq9
    | (have j0 := eq9 (σ x) X0 (σ y)
       grind)
    | exact resolve eq9 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = (M.op (M.op (M.op X1 X0) X3) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X0 X2) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op (τ (σ y)) (τ (σ x))) = (M.op (M.op (τ (σ y)) X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq42 eq9
    | exact resolve eq9 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (M.op (σ y) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq32 eq9
    | (have j0 := eq9 (σ y) (σ x) X0
       grind)
    | exact resolve eq9 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq51
    | exact resolve eq51 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq84 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op (M.op X1 X0) (M.op X0 X2)) = (k (M.op X1 X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 X0) (M.op X0 X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X1 X0) (M.op X0 X2)
       grind)
    | (have r₁ := eq12 (M.op X0 X0) (M.op X0 X2)
       have r₂ := eq9 X0 X0 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X1 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq47
    | exact resolve eq47 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq147 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq147 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq147 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq147 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq147 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq225 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op (σ x) X0) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq65 eq9
    | exact resolve eq9 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : (M.op (σ x) (τ (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (σ x) (τ (σ x))))) := by
    first
    | exact superpose eq63 eq65
    | exact resolve eq65 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq240 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op (τ (σ x)) X0) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq42 eq240
    | exact resolve eq240 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (τ (σ y)) X0)) = (M.op (M.op (τ (σ x)) X1) (M.op (τ (σ y)) (τ (σ x)))) := by
    intro X0 X1
    first
    | exact superpose eq67 eq240
    | exact resolve eq240 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq270 : ∀ X0 : G, (M.op (τ (σ x)) (τ (σ y))) = (M.op (M.op x y) (M.op (τ (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq261 X0 x
       have i₂ := eq9 (τ sF4) (τ sF5) x
       grind)
    | exact superpose eq9 eq261
    | exact resolve eq261 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq271 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op (τ (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq42 eq270
    | exact resolve eq270 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq270
  have eq293 : (M.op x y) = (M.op (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq257 eq271
    | exact resolve eq271 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257 eq271
  have eq303 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (τ (σ y)) (M.op x y)) ∨ (k (M.op x y) (τ (σ y))) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq293 eq13
    | (have j0 := eq13 (M.op x y) (τ (σ y))
       grind)
    | (have r₁ := eq13 (M.op x y) (τ (σ y))
       have r₂ := eq293
       grind)
    | exact resolve eq13 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq307 : (k (M.op x y) (τ (σ y))) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (τ (σ y)) (M.op x y)) := by grind
  clear eq303
  have eq369 : ∀ X0 X1 X2 X3 : G, (k X0 (M.op X1 X2)) = (M.op (M.op X1 X3) (M.op X0 (M.op X1 X2))) ∨ (M.op X0 (M.op X1 X2)) = X0 ∨ (M.op (M.op X1 X2) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 X1 X3 X2 X0
       have i₂ := eq14 X0 (M.op X1 X2)
       grind)
    | exact superpose eq14 eq62
    | (have j1 := eq14 X0 (M.op X1 X2)
       grind)
    | exact resolve eq62 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq409 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = (M.op (M.op X1 X3) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 X1 X3 X0 (M.op X0 X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X0 X1)) (M.op X0 X3)) = (M.op (M.op X2 X4) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 X2 X4 (M.op X0 X1) (M.op X0 X3)
       have i₂ := eq62 X0 X3 X1 X2
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op x y)) (M.op (τ (σ x)) X1)) = (M.op (M.op X0 X2) (M.op (M.op x y) X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq240 eq62
    | exact resolve eq62 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq413 : ∀ X0 X1 : G, (M.op (M.op X0 (τ (σ x))) (M.op x y)) = (M.op (M.op X0 X1) (M.op (τ (σ x)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq63 eq62
    | exact resolve eq62 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X0 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X2 X3
       have i₂ := eq62 X0 X1 X3 (M.op X2 X0)
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X0 X3))) ≠ X2 ∨ (M.op X2 (M.op X0 X3)) = (k X2 (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X2 (M.op X0 X3)
       have i₂ := eq62 X0 X1 X3 X2
       grind)
    | exact superpose eq62 eq12
    | (have j0 := eq12 X2 (M.op X0 X3)
       grind)
    | (have r₁ := eq12 (M.op (M.op X0 X2) (M.op X0 X2)) (M.op X0 X1)
       have r₂ := eq62 X0 X1 X2 (M.op X0 X2)
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq428 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) ≠ (M.op (M.op X0 X1) (M.op X2 (M.op X0 X3))) ∨ (M.op X0 X3) = (M.op X2 (M.op X0 X3)) ∨ (k (M.op X0 X3) X2) = (M.op (M.op X0 X3) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X0 X3) X2
       have i₂ := eq62 X0 X1 X3 X2
       grind)
    | exact superpose eq62 eq13
    | (have j0 := eq13 (M.op X0 X3) X2
       grind)
    | exact resolve eq13 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq444 : ∀ X0 : G, (M.op X0 (τ (σ x))) = (M.op (M.op X0 (τ (σ x))) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq413 X0 x
       have i₂ := eq9 X0 (τ sF4) x
       grind)
    | exact superpose eq9 eq413
    | exact resolve eq413 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq445 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op (τ (σ x)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq411 X0 X1 x
       have i₂ := eq9 X0 sF2 x
       grind)
    | exact superpose eq9 eq411
    | exact resolve eq411 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq446 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X1)) = (M.op (M.op X2 (M.op X0 X1)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq410 X0 X1 X2 X3 x
       have i₂ := eq9 X2 (M.op X0 X1) x
       grind)
    | exact superpose eq9 eq410
    | exact resolve eq410 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq447 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq409 X0 X1 X2 x
       have i₂ := eq9 X1 X0 x
       grind)
    | exact superpose eq9 eq409
    | exact resolve eq409 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq518 : ∀ X0 : G, (M.op X0 (τ (σ x))) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq445 eq9
    | exact resolve eq9 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq519 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op (M.op X0 X1) (τ (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq445 eq62
    | exact resolve eq62 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520 : (M.op (M.op x y) (τ (σ x))) = (M.op (τ (σ x)) (M.op x y)) := by
    first
    | exact superpose eq445 eq240
    | exact resolve eq240 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq548 : ∀ X0 X1 : G, (M.op (τ (σ x)) X0) = (M.op (M.op (τ (σ x)) X1) (M.op X0 (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq518 eq9
    | exact resolve eq9 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : ∀ X0 : G, (M.op (τ (σ x)) X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq240 eq548
    | exact resolve eq548 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq578 : ∀ X0 : G, (M.op (M.op x y) X0) ≠ X0 ∨ (k X0 (τ (σ x))) = (M.op X0 (τ (σ x))) := by
    intro X0
    first
    | exact superpose eq565 eq12
    | (have j0 := eq12 X0 (M.op x y)
       grind)
    | exact resolve eq12 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq599 : ∀ X0 : G, (M.op (M.op x y) X0) ≠ X0 ∨ (k X0 (τ (σ x))) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq518 eq578
    | (have j0 := eq578 X0
       grind)
    | exact resolve eq578 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq624 : (k (M.op x y) (τ (σ x))) = (M.op (M.op x y) (τ (σ x))) ∨ (M.op x y) = (M.op (M.op x y) (τ (σ x))) ∨ (M.op x y) = (M.op (M.op x y) (τ (σ x))) := by
    first
    | exact superpose eq520 eq14
    | (have j0 := eq14 (M.op x y) (τ (σ x))
       grind)
    | exact resolve eq14 eq520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq627 : (k (M.op x y) (τ (σ x))) = (M.op (M.op x y) (τ (σ x))) ∨ (M.op x y) = (M.op (M.op x y) (τ (σ x))) := by grind
  clear eq624
  have eq628 : (k (M.op x y) (τ (σ x))) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (τ (σ x))) := by
    first
    | exact superpose eq518 eq627
    | exact resolve eq627 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq637 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (k (M.op x y) (τ (σ x))) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq518 eq628
    | exact resolve eq628 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq641 : (k (M.op x y) (τ (σ x))) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq599 (M.op x y)
       grind)
    | (have r₁ := eq637
       have r₂ := eq599 (M.op x y)
       grind)
    | exact resolve eq637 eq599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599 eq637
  have eq690 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X3) (M.op X3 X4)) = (M.op (M.op (M.op X0 X1) X2) (M.op X3 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq66 X3 X0 X4 (M.op X2 (M.op X0 X1))
       have i₂ := eq62 X0 X3 X1 X2
       grind)
    | exact superpose eq62 eq66
    | exact resolve eq66 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq710 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X0 X1) X3)) (M.op (M.op (M.op X0 X1) X3) X4)) = (M.op (M.op (M.op (M.op X1 X0) (M.op (M.op X0 X1) X3)) X5) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq66 (M.op (M.op X0 X1) X3) (M.op X1 X0) X4 X5
       have i₂ := eq66 X1 X0 X2 X3
       grind)
    | exact superpose eq66 eq66
    | exact resolve eq66 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq733 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X1 X0)) = (M.op (M.op X0 X3) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 X0 X1 X3 X1
       have i₂ := eq66 X1 X0 (M.op X0 X3) X2
       grind)
    | exact superpose eq66 eq62
    | exact resolve eq62 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq739 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op (M.op (M.op X0 X1) X2) (M.op X1 X0)) ∨ (M.op X0 X1) = (M.op (M.op X1 X3) (M.op X0 X1)) ∨ (k (M.op X0 X1) (M.op X1 X3)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X0 X1) (M.op X1 X3)
       have i₂ := eq66 X1 X0 X3 X2
       grind)
    | exact superpose eq66 eq13
    | (have j0 := eq13 (M.op X0 X1) (M.op X1 X3)
       grind)
    | (have r₁ := eq13 (M.op (M.op X1 X0) (M.op X0 X2)) (M.op X0 X1)
       have r₂ := eq66 X0 X1 X2 (M.op X0 X2)
       grind)
    | exact resolve eq13 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq745 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) (M.op (M.op X0 X1) X3)) = (M.op (M.op X1 X4) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 X1 X4 X0 (M.op (M.op X0 X1) X3)
       have i₂ := eq66 X1 X0 X2 X3
       grind)
    | exact superpose eq66 eq62
    | exact resolve eq62 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : ∀ X0 X1 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq745 X0 X1 x X3 x
       have i₂ := eq420 X1 x X0 x
       grind)
    | exact superpose eq420 eq745
    | exact resolve eq745 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420 eq745
  have eq761 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op (M.op (M.op X0 X1) X2) (M.op X1 X0)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k (M.op X0 X1) (M.op X1 X3)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq739 X0 X1 X2 X3
       have i₂ := eq9 X1 X0 X3
       grind)
    | exact superpose eq9 eq739
    | (have j0 := eq739 X0 X1 X2 X3
       grind)
    | exact resolve eq739 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739
  have eq788 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X0 X1) X3)) (M.op (M.op (M.op X0 X1) X3) X4)) = (M.op (M.op (M.op (M.op X1 X0) (M.op (M.op X0 X1) X3)) X5) (M.op X0 X1)) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq710 X0 X1 x X3 X4 X5
       have i₂ := eq447 X1 X0 x
       grind)
    | exact superpose eq447 eq710
    | exact resolve eq710 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq807 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X0 X1) X2) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq690 X0 X1 X2 X3 x
       have i₂ := eq447 X3 X0 x
       grind)
    | exact superpose eq447 eq690
    | exact resolve eq690 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq853 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op X1 X0) (M.op (M.op (M.op X0 X1) X3) X4)) = (M.op (M.op (M.op X1 X0) X5) (M.op X0 X1)) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq788 X0 X1 X3 X4 X5
       have i₂ := eq757 X0 X1 X3
       grind)
    | exact superpose eq757 eq788
    | exact resolve eq788 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq885 : ∀ X0 X1 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op (M.op X0 X1) X3) X4)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq853 X0 X1 X3 X4 x
       have i₂ := eq807 X1 X0 x X0
       grind)
    | exact superpose eq807 eq853
    | exact resolve eq853 eq807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq919 : (M.op x y) ≠ (k (M.op x y) (τ (σ x))) ∨ (k (M.op x y) (M.op x y)) = (k (M.op x y) (τ (σ x))) := by
    first
    | exact superpose eq641 eq12
    | exact resolve eq12 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq921 : (k (M.op x y) (M.op x y)) = (k (M.op x y) (τ (σ x))) ∨ (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (M.op x y) = (k (M.op x y) (τ (σ x))) := by
    first
    | exact superpose eq641 eq14
    | exact resolve eq14 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq926 : (k (M.op x y) (M.op x y)) = (k (M.op x y) (τ (σ x))) ∨ (M.op x y) = (k (M.op x y) (τ (σ x))) := by grind
  clear eq921
  have eq928 : (k (M.op x y) (M.op x y)) = (k (M.op x y) (τ (σ x))) := by
    first
    | (have r₁ := eq919
       have r₂ := eq926
       grind)
    | exact resolve eq919 eq926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919 eq926
  have eq990 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op (σ x) (τ (σ x))) (τ (σ x))) := by
    first
    | exact superpose eq235 eq519
    | exact resolve eq519 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq996 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op (M.op X0 X1) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq519 eq518
    | exact resolve eq518 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1000 : ∀ X0 X1 X2 : G, (M.op (τ (σ x)) (M.op X0 X1)) = (M.op (M.op (τ (σ x)) X2) (M.op X0 (M.op x y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq519 eq9
    | exact resolve eq9 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1013 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (τ (σ x)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq240 eq1000
    | exact resolve eq1000 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240 eq1000
  have eq1019 : (M.op (σ x) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | exact superpose eq519 eq990
    | exact resolve eq990 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519 eq990
  have eq1041 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq565 eq1013
    | exact resolve eq1013 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq1143 : ∀ X0 : G, (M.op (M.op x y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) X0) (M.op (σ x) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1019 eq9
    | exact resolve eq9 eq1019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1155 : (M.op (M.op x y) (σ x)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1143 x
       have i₂ := eq9 sF2 sF4 x
       grind)
    | exact superpose eq9 eq1143
    | exact resolve eq1143 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq1163 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op x y) (σ x))) := by
    intro X0
    first
    | exact superpose eq1155 eq9
    | exact resolve eq9 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155
  have eq1178 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op x y) (σ x))) := by
    intro X0
    first
    | exact superpose eq1019 eq1163
    | exact resolve eq1163 eq1019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019 eq1163
  have eq1480 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X1 X2)) ≠ (M.op (M.op X1 X0) (M.op (M.op X0 X1) X3)) ∨ (M.op (M.op (M.op X1 X0) (M.op (M.op X0 X1) X3)) (M.op (M.op (M.op X0 X1) X3) X4)) = (k (M.op (M.op X1 X0) (M.op (M.op X0 X1) X3)) (M.op (M.op (M.op X0 X1) X3) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq84 (M.op (M.op X0 X1) X3) (M.op X1 X0) X4
       have i₂ := eq66 X1 X0 X2 X3
       grind)
    | exact superpose eq66 eq84
    | (have j0 := eq84 (M.op (M.op X0 X1) X3) (M.op X1 X0) X4
       grind)
    | exact resolve eq84 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq1520 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (k (M.op X0 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq1525 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1520 X0 X1
       have i₂ := eq447 X0 X0 X1
       grind)
    | exact superpose eq447 eq1520
    | exact resolve eq1520 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1520
  have eq1563 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) ≠ (M.op (M.op X0 X1) (M.op X1 X2)) ∨ (M.op (M.op (M.op X1 X0) (M.op (M.op X0 X1) X3)) (M.op (M.op (M.op X0 X1) X3) X4)) = (k (M.op (M.op X1 X0) (M.op (M.op X0 X1) X3)) (M.op (M.op (M.op X0 X1) X3) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1480 X0 X1 X2 X3 X4
       have i₂ := eq757 X0 X1 X3
       grind)
    | exact superpose eq757 eq1480
    | (have j0 := eq1480 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq1480 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1480
  have eq1594 : ∀ X0 X1 X3 X4 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op (M.op (M.op X1 X0) (M.op (M.op X0 X1) X3)) (M.op (M.op (M.op X0 X1) X3) X4)) = (k (M.op (M.op X1 X0) (M.op (M.op X0 X1) X3)) (M.op (M.op (M.op X0 X1) X3) X4)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq1563 X0 X1 x X3 X4
       have i₂ := eq447 X1 X0 x
       grind)
    | exact superpose eq447 eq1563
    | (have j0 := eq1563 X0 X1 x X3 X4
       grind)
    | (have r₁ := eq1563 X1 X1 x X3 X4
       have r₂ := eq447 X1 X1 x
       grind)
    | exact resolve eq1563 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1563
  have eq1618 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X1 X0) (M.op (M.op (M.op X0 X1) X3) X4)) = (k (M.op X1 X0) (M.op (M.op (M.op X0 X1) X3) X4)) ∨ (M.op X0 X1) ≠ (M.op X1 X0) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq1594 X0 X1 X3 X4
       have i₂ := eq757 X0 X1 X3
       grind)
    | exact superpose eq757 eq1594
    | (have j0 := eq1594 X0 X1 X3 X4
       grind)
    | exact resolve eq1594 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594
  have eq1627 : ∀ X0 X1 X3 X4 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k (M.op X1 X0) (M.op (M.op (M.op X0 X1) X3) X4)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq1618 X0 X1 X3 X4
       have i₂ := eq885 X0 X1 X3 X4
       grind)
    | exact superpose eq885 eq1618
    | (have j0 := eq1618 X0 X1 X3 X4
       grind)
    | exact resolve eq1618 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885 eq1618
  have eq2777 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (M.op (σ x) X1) (M.op (σ y) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq69 eq225
    | exact resolve eq225 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2829 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq2777 X0 x
       have i₂ := eq9 sF4 sF5 x
       grind)
    | exact superpose eq9 eq2777
    | exact resolve eq2777 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2777
  have eq2833 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq32 eq2829
    | (have j0 := eq2829 X0
       grind)
    | exact resolve eq2829 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2829
  have eq2938 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq447 (M.op X0 X2) (M.op X1 X0) X2
       have i₂ := eq447 X0 X1 X2
       grind)
    | exact superpose eq447 eq447
    | exact resolve eq447 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2995 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) (M.op (σ x) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq1178 eq447
    | exact resolve eq447 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq3041 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 X1 X2 X1
       have i₂ := eq447 X1 X0 (M.op X0 X2)
       grind)
    | exact superpose eq447 eq62
    | exact resolve eq62 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq3045 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq225 X0 X0
       have i₂ := eq447 X0 sF4 sF6
       grind)
    | exact superpose eq447 eq225
    | exact resolve eq225 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq3095 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (M.op x y))) = (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2995 X0 X1
       have i₂ := eq3041 X0 (M.op sF4 sF2) (M.op sF6 X1)
       grind)
    | exact superpose eq3041 eq2995
    | exact resolve eq2995 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2995
  have eq3114 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2938 X0 X1 X2 X3
       have i₂ := eq3041 X0 (M.op (M.op X1 X2) X3) X1
       grind)
    | exact superpose eq3041 eq2938
    | exact resolve eq2938 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2938
  have eq3128 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (M.op x y))) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq3045 eq3095
    | exact resolve eq3095 eq3045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3095
  have eq3142 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq3114 X0 X1 x X3
       have i₂ := eq3041 X1 X3 x
       grind)
    | exact superpose eq3041 eq3114
    | exact resolve eq3114 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3114
  have eq3543 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq32 eq3128
    | (have j0 := eq3128 X0 (σ y)
       grind)
    | exact resolve eq3128 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3128
  have eq3715 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq3543 X0
       have i₂ := eq3142 X0 sF4 sF2
       grind)
    | exact superpose eq3142 eq3543
    | (have j1 := eq3142 X0 (σ x) (σ y)
       grind)
    | exact resolve eq3543 eq3142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3543
  have eq4248 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 X0)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq125 (M.op X0 X1) (M.op X0 X0)
       have i₂ := eq1525 X0 X1
       grind)
    | exact superpose eq1525 eq125
    | exact resolve eq125 eq1525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23867 : (τ (M.op (σ x) (σ x))) = (k (τ (M.op (σ x) (σ x))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq32 eq4248
    | (have j0 := eq4248 (σ x) (σ y)
       grind)
    | exact resolve eq4248 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23881 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X1))) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq161 (τ (M.op X0 X0)) (τ (M.op X0 X1))
       have i₂ := eq4248 X0 X1
       grind)
    | exact superpose eq4248 eq161
    | (have j0 := eq161 (τ (M.op X0 X0)) (τ (M.op X0 X1))
       grind)
    | (have r₁ := eq161 (τ (M.op X0 X0)) (τ (M.op X0 X1))
       have r₂ := eq4248 X0 X1
       grind)
    | exact resolve eq161 eq4248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4248
  have eq23882 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq23881 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23881
  have eq23883 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq23882 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23882
  have eq24429 : (τ (M.op (σ x) (σ x))) ≠ (τ (M.op (σ x) (σ x))) ∨ (τ (M.op (σ x) (σ x))) = (M.op (τ (M.op (σ x) (σ x))) (τ (M.op (σ x) (σ y)))) ∨ (τ (M.op (σ x) (σ x))) = (M.op (τ (M.op (σ x) (σ x))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq23867 eq161
    | (have j0 := eq161 (τ (M.op (σ x) (σ x))) (τ (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq161 (τ (M.op (σ x) (σ x))) (τ (M.op (σ x) (σ y)))
       have r₂ := eq23867
       grind)
    | exact resolve eq161 eq23867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23867
  have eq24430 : (τ (M.op (σ x) (σ x))) ≠ (τ (M.op (σ x) (σ x))) ∨ (τ (M.op (σ x) (σ x))) = (M.op (τ (M.op (σ x) (σ x))) (τ (M.op (σ x) (σ y)))) := by grind
  clear eq24429
  have eq24431 : (τ (M.op (σ x) (σ x))) = (M.op (τ (M.op (σ x) (σ x))) (τ (M.op (σ x) (σ y)))) := by grind
  clear eq24430
  have eq26974 : (k (M.op x y) (τ (σ y))) = (M.op (M.op x y) (k (M.op x y) (τ (σ y)))) ∨ (M.op x y) = (M.op (τ (σ y)) (M.op x y)) := by
    first
    | exact superpose eq307 eq1041
    | exact resolve eq1041 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307 eq1041
  have eq63523 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (M.op X1 (M.op (σ x) (σ y)))) ≠ X1 ∨ (M.op X1 (M.op (σ x) (σ y))) = (k X1 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq32 eq427
    | (have j0 := eq427 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq427 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63789 : ∀ X1 : G, (M.op (σ x) (M.op X1 (M.op (σ x) (σ y)))) ≠ X1 ∨ (M.op X1 (M.op (σ x) (σ y))) = (k X1 (M.op (σ x) (σ y))) := by
    intro X1
    first
    | (have i₁ := eq63523 x X1
       have i₂ := eq3041 sF4 (M.op X1 sF6) x
       grind)
    | exact superpose eq3041 eq63523
    | (have j0 := eq63523 x X1
       grind)
    | exact resolve eq63523 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63523
  have eq64158 : ∀ X1 : G, (M.op (σ x) X1) ≠ X1 ∨ (M.op X1 (M.op (σ x) (σ y))) = (k X1 (M.op (σ x) (σ y))) := by
    intro X1
    first
    | (have i₁ := eq63789 X1
       have i₂ := eq3142 sF4 X1 sF6
       grind)
    | exact superpose eq3142 eq63789
    | (have j0 := eq63789 X1
       grind)
    | exact resolve eq63789 eq3142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63789
  have eq64445 : ∀ X1 : G, (M.op (σ x) X1) ≠ X1 ∨ (k X1 (M.op (σ x) (σ y))) = (M.op X1 (σ x)) := by
    intro X1
    first
    | exact superpose eq3715 eq64158
    | (have j0 := eq64158 X1
       grind)
    | exact resolve eq64158 eq3715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64158
  have eq65153 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3715 eq64445
    | (have j0 := eq64445 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq64445 eq3715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64445
  have eq65154 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3045 eq65153
    | exact resolve eq65153 eq3045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65153
  have eq65368 : ∀ X0 X1 : G, (τ (M.op (σ x) (σ x))) ≠ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ x)))) ∨ (τ (M.op (σ x) (σ x))) = (k (τ (M.op (σ x) (σ x))) (M.op (M.op (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ x)))) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq24431 eq1627
    | exact resolve eq1627 eq24431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1627
  have eq65422 : ∀ X1 : G, (τ (M.op (σ x) (σ x))) = (k (τ (M.op (σ x) (σ x))) (M.op (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ x)))) X1)) ∨ (τ (M.op (σ x) (σ x))) ≠ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ x)))) := by
    intro X1
    first
    | (have i₁ := eq65368 x X1
       have i₂ := eq3041 (M.op (τ sF6) (τ (M.op sF4 sF4))) X1 x
       grind)
    | exact superpose eq3041 eq65368
    | exact resolve eq65368 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65368
  have eq65641 : ∀ X1 : G, (τ (M.op (σ x) (σ x))) = (k (τ (M.op (σ x) (σ x))) (M.op (τ (M.op (σ x) (σ y))) X1)) ∨ (τ (M.op (σ x) (σ x))) ≠ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ x)))) := by
    intro X1
    first
    | (have i₁ := eq65422 X1
       have i₂ := eq3041 (τ sF6) X1 (τ (M.op sF4 sF4))
       grind)
    | exact superpose eq3041 eq65422
    | exact resolve eq65422 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65422
  have eq142045 : ∀ X0 X1 : G, (M.op (M.op (σ x) X1) (M.op X0 (M.op (σ x) (σ y)))) = (k X0 (M.op (σ x) (σ y))) ∨ (M.op X0 (M.op (σ x) (σ y))) = X0 ∨ (M.op (M.op (σ x) (σ y)) X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq32 eq369
    | (have j0 := eq369 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq369 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142823 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) ∨ (M.op X0 (M.op (σ x) (σ y))) = X0 ∨ (M.op (M.op (σ x) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq142045 X0 x
       have i₂ := eq3041 sF4 (M.op X0 sF6) x
       grind)
    | exact superpose eq3041 eq142045
    | (have j0 := eq142045 X0 x
       grind)
    | exact resolve eq142045 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142045
  have eq143526 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (M.op (σ x) (σ y))) ∨ (M.op X0 (M.op (σ x) (σ y))) = X0 ∨ (M.op (M.op (σ x) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq142823 x
       have i₂ := eq3142 sF4 x sF6
       grind)
    | exact superpose eq3142 eq142823
    | (have j0 := eq142823 X0
       grind)
    | exact resolve eq142823 eq3142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142823
  have eq144147 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (M.op (σ x) X0) = (k X0 (M.op (σ x) (σ y))) ∨ (M.op (M.op (σ x) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq3715 eq143526
    | (have j0 := eq143526 X0
       grind)
    | exact resolve eq143526 eq3715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143526
  have eq144722 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (M.op (σ x) (σ y))) ∨ (M.op X0 (σ x)) = X0 ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq3045 eq144147
    | (have j0 := eq144147 X0
       grind)
    | exact resolve eq144147 eq3045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144147
  have eq260952 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) ≠ (M.op (M.op (σ x) X0) (M.op X1 (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op X1 (M.op (σ x) (σ y))) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq32 eq428
    | (have j0 := eq428 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq428 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261105 : ∀ X0 X1 : G, (M.op X0 (τ (σ x))) ≠ (M.op (M.op X0 X1) (M.op (τ (σ x)) X0)) ∨ (M.op (τ (σ x)) X0) = (M.op X0 (τ (σ x))) ∨ (k (M.op X0 (τ (σ x))) (M.op x y)) = (M.op (M.op X0 (τ (σ x))) (M.op X0 (τ (σ x)))) := by
    intro X0 X1
    first
    | exact superpose eq63 eq428
    | (have j0 := eq428 X0 X1 (M.op x y) (τ (σ x))
       grind)
    | exact resolve eq428 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq428
  have eq261240 : ∀ X0 : G, (M.op (τ (σ x)) X0) = (M.op X0 (τ (σ x))) ∨ (k (M.op X0 (τ (σ x))) (M.op x y)) = (M.op (M.op X0 (τ (σ x))) (M.op X0 (τ (σ x)))) := by
    intro X0
    first
    | (have j0 := eq261105 X0 x
       grind)
    | (have r₁ := eq261105 X0 x
       have r₂ := eq9 X0 (τ (σ x)) x
       grind)
    | exact resolve eq261105 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261105
  have eq261389 : ∀ X1 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (M.op X1 (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op X1 (M.op (σ x) (σ y))) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) X1) := by
    intro X1
    first
    | (have i₁ := eq260952 x X1
       have i₂ := eq3041 sF4 (M.op X1 sF6) x
       grind)
    | exact superpose eq3041 eq260952
    | (have j0 := eq260952 x X1
       grind)
    | exact resolve eq260952 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260952
  have eq261890 : ∀ X0 : G, (M.op (τ (σ x)) X0) = (M.op X0 (M.op x y)) ∨ (k (M.op X0 (τ (σ x))) (M.op x y)) = (M.op (M.op X0 (τ (σ x))) (M.op X0 (τ (σ x)))) := by
    intro X0
    first
    | exact superpose eq518 eq261240
    | (have j0 := eq261240 X0
       grind)
    | exact resolve eq261240 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261240
  have eq262035 : ∀ X1 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) X1) ∨ (M.op (σ x) (σ y)) = (M.op X1 (M.op (σ x) (σ y))) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) X1) := by
    intro X1
    first
    | (have i₁ := eq261389 X1
       have i₂ := eq3142 sF4 X1 sF6
       grind)
    | exact superpose eq3142 eq261389
    | (have j0 := eq261389 X1
       grind)
    | (have r₁ := eq261389 (σ y)
       have r₂ := eq3142 (σ x) (σ y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq261389 eq3142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261389
  have eq262434 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ (k (M.op X0 (τ (σ x))) (M.op x y)) = (M.op (M.op X0 (τ (σ x))) (M.op X0 (τ (σ x)))) := by
    intro X0
    first
    | exact superpose eq565 eq261890
    | (have j0 := eq261890 X0
       grind)
    | exact resolve eq261890 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261890
  have eq262572 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op X1 (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ x) X1) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) X1) := by
    intro X1
    first
    | exact superpose eq3715 eq262035
    | (have j0 := eq262035 X1
       grind)
    | exact resolve eq262035 eq3715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262035
  have eq262952 : ∀ X0 : G, (k (M.op X0 (τ (σ x))) (M.op x y)) = (M.op X0 (M.op X0 (τ (σ x)))) ∨ (M.op X0 (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq262434 X0
       have i₂ := eq3041 X0 (M.op X0 (τ sF4)) (τ sF4)
       grind)
    | exact superpose eq3041 eq262434
    | (have j0 := eq262434 X0
       grind)
    | exact resolve eq262434 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262434
  have eq263078 : ∀ X1 : G, (k (M.op (σ x) (σ y)) X1) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op X1 (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ x) X1) := by
    intro X1
    first
    | exact superpose eq3045 eq262572
    | (have j0 := eq262572 X1
       grind)
    | exact resolve eq262572 eq3045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262572
  have eq263443 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 (τ (σ x))) (M.op x y)) ∨ (M.op X0 (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq262952 x
       have i₂ := eq3142 x x (τ sF4)
       grind)
    | exact superpose eq3142 eq262952
    | (have j0 := eq262952 X0
       grind)
    | exact resolve eq262952 eq3142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262952
  have eq263563 : ∀ X1 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) X1) ∨ (M.op (σ x) (σ y)) = (M.op X1 (σ x)) ∨ (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ y)) X1) := by
    intro X1
    first
    | exact superpose eq3715 eq263078
    | (have j0 := eq263078 X1
       grind)
    | exact resolve eq263078 eq3715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263078
  have eq263885 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 (M.op x y)) (M.op x y)) ∨ (M.op X0 (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq518 eq263443
    | (have j0 := eq263443 X0
       grind)
    | exact resolve eq263443 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263443
  have eq265887 : ∀ X0 : G, (k (M.op X0 (M.op x y)) (M.op x y)) ≠ X0 ∨ (k X0 X0) = (k (M.op X0 (M.op x y)) (M.op x y)) ∨ (M.op X0 (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq263885 X0
       grind)
    | (have i₁ := eq12 (M.op x y) X0
       have i₂ := eq263885 X0
       grind)
    | exact superpose eq263885 eq12
    | (have j1 := eq263885 X0
       grind)
    | exact resolve eq12 eq263885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265889 : ∀ X0 : G, (k X0 X0) = (k (M.op X0 (M.op x y)) (M.op x y)) ∨ (k (M.op X0 (M.op x y)) (M.op x y)) = X0 ∨ (k (M.op X0 (M.op x y)) (M.op x y)) = X0 ∨ (M.op X0 (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0
       have i₂ := eq263885 X0
       grind)
    | (have i₁ := eq14 (M.op x y) X0
       have i₂ := eq263885 X0
       grind)
    | exact superpose eq263885 eq14
    | (have j1 := eq263885 X0
       grind)
    | exact resolve eq14 eq263885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266366 : ∀ X0 : G, (k X0 X0) = (k (M.op X0 (M.op x y)) (M.op x y)) ∨ (k (M.op X0 (M.op x y)) (M.op x y)) = X0 ∨ (M.op X0 (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have j0 := eq265889 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265889
  have eq266734 : ∀ X0 : G, (k X0 X0) = (k (M.op X0 (M.op x y)) (M.op x y)) ∨ (M.op X0 (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have j0 := eq265887 X0
       have j1 := eq266366 X0
       grind)
    | (have r₁ := eq265887 X0
       have r₂ := eq266366 X0
       grind)
    | exact resolve eq265887 eq266366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265887 eq266366
  have eq268108 : ∀ X0 X1 : G, (τ (M.op (σ x) (σ x))) ≠ (M.op (M.op (τ (M.op (σ x) (σ x))) X0) (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ x))))) ∨ (τ (M.op (σ x) (σ x))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ x)))) ∨ (M.op (τ (M.op (σ x) (σ x))) (τ (M.op (σ x) (σ x)))) = (k (τ (M.op (σ x) (σ x))) (M.op (τ (M.op (σ x) (σ y))) X1)) := by
    intro X0 X1
    first
    | exact superpose eq24431 eq761
    | exact resolve eq761 eq24431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq269124 : ∀ X1 : G, (τ (M.op (σ x) (σ x))) ≠ (M.op (τ (M.op (σ x) (σ x))) (τ (M.op (σ x) (σ y)))) ∨ (τ (M.op (σ x) (σ x))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ x)))) ∨ (M.op (τ (M.op (σ x) (σ x))) (τ (M.op (σ x) (σ x)))) = (k (τ (M.op (σ x) (σ x))) (M.op (τ (M.op (σ x) (σ y))) X1)) := by
    intro X1
    first
    | (have i₁ := eq268108 x X1
       have i₂ := eq9 (τ (M.op sF4 sF4)) (τ sF6) x
       grind)
    | exact superpose eq9 eq268108
    | (have j0 := eq268108 x X1
       grind)
    | exact resolve eq268108 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268108
  have eq269731 : ∀ X1 : G, (τ (M.op (σ x) (σ x))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ x)))) ∨ (M.op (τ (M.op (σ x) (σ x))) (τ (M.op (σ x) (σ x)))) = (k (τ (M.op (σ x) (σ x))) (M.op (τ (M.op (σ x) (σ y))) X1)) := by
    intro X1
    first
    | (have j0 := eq269124 X1
       grind)
    | (have r₁ := eq269124 X1
       have r₂ := eq24431
       grind)
    | exact resolve eq269124 eq24431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24431 eq269124
  have eq270267 : ∀ X1 : G, (τ (M.op (σ x) (σ x))) = (k (τ (M.op (σ x) (σ x))) (M.op (τ (M.op (σ x) (σ y))) X1)) ∨ (τ (M.op (σ x) (σ x))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ x)))) := by
    intro X1
    first
    | (have i₁ := eq269731 X1
       have i₂ := eq23883 sF4 sF4
       grind)
    | exact superpose eq23883 eq269731
    | exact resolve eq269731 eq23883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23883 eq269731
  have eq270777 : ∀ X1 : G, (τ (M.op (σ x) (σ x))) = (k (τ (M.op (σ x) (σ x))) (M.op (τ (M.op (σ x) (σ y))) X1)) := by
    intro X1
    first
    | (have j0 := eq270267 X1
       have j1 := eq65641 X1
       grind)
    | (have r₁ := eq270267 X1
       have r₂ := eq65641 X1
       grind)
    | exact resolve eq270267 eq65641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65641 eq270267
  have eq284265 : ∀ X0 : G, (σ (τ (M.op (σ x) (σ x)))) = (k (σ (τ (M.op (σ x) (σ x)))) (σ (M.op (τ (M.op (σ x) (σ y))) X0))) := by
    intro X0
    first
    | exact superpose eq270777 eq15
    | exact resolve eq15 eq270777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270777
  have eq284318 : ∀ X0 : G, (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ x)) (σ (M.op (τ (M.op (σ x) (σ y))) X0))) := by
    intro X0
    first
    | (have i₁ := eq284265 X0
       have i₂ := eq35 (M.op sF4 sF4)
       grind)
    | exact superpose eq35 eq284265
    | exact resolve eq284265 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284265
  have eq287881 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ (M.op X0 (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq266734 eq263885
    | (have j0 := eq263885 X0
       have j1 := eq266734 X0
       grind)
    | exact resolve eq263885 eq266734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263885 eq266734
  have eq287910 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq287881 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287881
  have eq288487 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op x y))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq287910 X0
       grind)
    | exact superpose eq287910 eq9
    | (have j1 := eq287910 X0
       grind)
    | exact resolve eq9 eq287910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288489 : ∀ X0 : G, (M.op X0 (M.op x y)) ≠ X0 ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq287910 X0
       grind)
    | exact superpose eq287910 eq12
    | (have j0 := eq12 X0 (M.op x y)
       have j1 := eq287910 X0
       grind)
    | exact resolve eq12 eq287910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288491 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ (M.op X0 (M.op x y)) = X0 ∨ (M.op X0 (M.op x y)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0
       have i₂ := eq287910 X0
       grind)
    | exact superpose eq287910 eq14
    | (have j0 := eq14 X0 X0
       have j1 := eq287910 X0
       grind)
    | exact resolve eq14 eq287910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288662 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ (M.op X0 (M.op x y)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq288491 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288491
  have eq288832 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq288489 X0
       have j1 := eq288662 X0
       grind)
    | (have r₁ := eq288489 X0
       have r₂ := eq288662 X0
       grind)
    | exact resolve eq288489 eq288662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288489 eq288662
  have eq288834 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op X0 (M.op X1 (M.op x y))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq288487 X0 X1
       have i₂ := eq3041 X0 (M.op X1 sF2) sF2
       grind)
    | exact superpose eq3041 eq288487
    | (have j0 := eq288487 X0 X1
       grind)
    | exact resolve eq288487 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288487
  have eq289306 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op x y) X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq288834 X0 X1
       have i₂ := eq3142 X0 X1 sF2
       grind)
    | exact superpose eq3142 eq288834
    | (have j0 := eq288834 X0 X1
       grind)
    | exact resolve eq288834 eq3142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288834
  have eq304084 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq287910 sF2
       have i₂ := eq288832 sF2
       grind)
    | exact superpose eq288832 eq287910
    | (have j0 := eq287910 X0
       have j1 := eq288832 X0
       grind)
    | exact resolve eq287910 eq288832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287910
  have eq304091 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k X0 (M.op x y)) (M.op X1 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq288832 X0
       grind)
    | exact superpose eq288832 eq9
    | (have j1 := eq288832 X0
       grind)
    | exact resolve eq9 eq288832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288832
  have eq304476 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq304084 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304084
  have eq304778 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k X0 (M.op x y)) X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq304091 x X1
       have i₂ := eq3142 (k x sF2) X1 x
       grind)
    | exact superpose eq3142 eq304091
    | (have j0 := eq304091 X0 X1
       grind)
    | exact resolve eq304091 eq3142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304091
  have eq313289 : ∀ X0 : G, (k X0 X0) ≠ (M.op (M.op x y) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq289306 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289306
  have eq361757 : ∀ X0 X1 : G, (k X0 (M.op x y)) = (M.op (k X0 (M.op x y)) (M.op X0 X1)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq447 X0 X0 x
       have i₂ := eq304476 X0
       grind)
    | exact superpose eq304476 eq447
    | (have j1 := eq304476 X0
       grind)
    | exact resolve eq447 eq304476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362108 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (k X0 (M.op x y)) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq361757 x x
       have i₂ := eq3142 (k x sF2) x x
       grind)
    | exact superpose eq3142 eq361757
    | (have j0 := eq361757 X0 x
       grind)
    | exact resolve eq361757 eq3142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361757
  have eq370087 : ∀ X0 : G, (k X0 (M.op x y)) ≠ (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq313289 sF2
       have i₂ := eq304476 sF2
       grind)
    | exact superpose eq304476 eq313289
    | (have j0 := eq313289 X0
       have j1 := eq304476 X0
       grind)
    | (have r₁ := eq313289 (M.op x y)
       have r₂ := eq304476 (M.op x y)
       grind)
    | exact resolve eq313289 eq304476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304476 eq313289
  have eq370138 : ∀ X0 : G, (k X0 (M.op x y)) ≠ (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq370087 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370087
  have eq484332 : (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq144722 eq3715
    | (have j1 := eq144722 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq3715 eq144722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144722
  have eq484385 : (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have j1 := eq263563 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq484332
       have r₂ := eq263563 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq484332 eq263563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263563 eq484332
  have eq484689 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3045 eq484385
    | exact resolve eq484385 eq3045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484385
  have eq484897 : (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq484689
       have r₂ := eq65154
       grind)
    | exact resolve eq484689 eq65154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65154 eq484689
  have eq485178 : ∀ X0 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ (M.op (τ (M.op (σ x) (σ y))) X0))) := by
    intro X0
    first
    | exact superpose eq484897 eq284318
    | exact resolve eq284318 eq484897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284318
  have eq485211 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq484897 eq9
    | exact resolve eq9 eq484897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq485213 : (σ x) ≠ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (k (σ x) (σ x)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq484897 eq12
    | exact resolve eq12 eq484897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq485215 : (k (σ x) (σ x)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq484897 eq14
    | exact resolve eq14 eq484897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq485288 : ∀ X0 X1 : G, (M.op (M.op (σ x) X1) (σ x)) = (M.op (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq484897 eq733
    | exact resolve eq733 eq484897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq485296 : ∀ X0 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) := by
    intro X0
    first
    | exact superpose eq484897 eq757
    | exact resolve eq757 eq484897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757 eq484897
  have eq485399 : (k (σ x) (σ x)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by grind
  clear eq485215
  have eq485465 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq485296 x
       have i₂ := eq3142 (k sF6 sF6) (k sF6 sF6) x
       grind)
    | exact superpose eq3142 eq485296
    | exact resolve eq485296 eq3142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485296
  have eq485471 : ∀ X1 : G, (M.op (M.op (σ x) X1) (σ x)) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X1
    first
    | (have i₁ := eq485288 x X1
       have i₂ := eq3041 (k sF6 sF6) (k sF6 sF6) x
       grind)
    | exact superpose eq3041 eq485288
    | exact resolve eq485288 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485288
  have eq485540 : (k (σ x) (σ x)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq485213
       have r₂ := eq485399
       grind)
    | exact resolve eq485213 eq485399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485213 eq485399
  have eq485542 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | (have i₁ := eq485211 x
       have i₂ := eq3142 (k sF6 sF6) x sF4
       grind)
    | exact superpose eq3142 eq485211
    | exact resolve eq485211 eq3142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485211
  have eq485616 : ∀ X1 : G, (M.op (M.op (σ x) X1) (σ x)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X1
    first
    | exact superpose eq485465 eq485471
    | exact resolve eq485471 eq485465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485465 eq485471
  have eq485673 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (k (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq485540 eq485542
    | exact resolve eq485542 eq485540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485542
  have eq485724 : ∀ X1 : G, (M.op (M.op (σ x) X1) (σ x)) = (k (σ x) (σ x)) := by
    intro X1
    first
    | exact superpose eq485540 eq485616
    | exact resolve eq485616 eq485540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485616
  have eq485801 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq485724 x
       have i₂ := eq3041 sF4 sF4 x
       grind)
    | exact superpose eq3041 eq485724
    | exact resolve eq485724 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485724
  have eq485915 : (τ (k (σ x) (σ x))) = (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq485540 eq125
    | exact resolve eq125 eq485540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486000 : (k (τ (σ x)) (τ (σ x))) = (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq485915
       have i₂ := eq125 sF4 sF4
       grind)
    | exact superpose eq125 eq485915
    | exact resolve eq485915 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485915
  have eq486590 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op X0 (σ x)) (k (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq485801 eq447
    | exact resolve eq447 eq485801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486817 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (k (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq486590 X0
       have i₂ := eq3041 X0 (k sF4 sF4) sF4
       grind)
    | exact superpose eq3041 eq486590
    | exact resolve eq486590 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486590
  have eq508278 : ∀ X0 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ≠ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ (M.op (τ (M.op (σ x) (σ y))) X0))) ∨ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ (M.op (τ (M.op (σ x) (σ y))) X0))) := by
    intro X0
    first
    | exact superpose eq485178 eq161
    | (have j0 := eq161 (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ (M.op (τ (M.op (σ x) (σ y))) X0))
       grind)
    | (have r₁ := eq161 (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ (M.op (τ (M.op (σ x) (σ y))) X0))
       have r₂ := eq485178 X0
       grind)
    | exact resolve eq161 eq485178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161 eq485178
  have eq508279 : ∀ X0 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ≠ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ (M.op (τ (M.op (σ x) (σ y))) X0))) := by
    intro X0
    first
    | (have j0 := eq508278 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508278
  have eq508280 : ∀ X0 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ (M.op (τ (M.op (σ x) (σ y))) X0))) := by
    intro X0
    first
    | (have j0 := eq508279 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508279
  have eq508282 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (k (σ x) (σ x)) (σ (M.op (τ (M.op (σ x) (σ y))) X0))) := by
    intro X0
    first
    | exact superpose eq485540 eq508280
    | exact resolve eq508280 eq485540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485540 eq508280
  have eq508299 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) (σ (M.op (τ (M.op (σ x) (σ y))) X0))) := by
    intro X0
    first
    | exact superpose eq485673 eq508282
    | exact resolve eq508282 eq485673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508282
  have eq602365 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x y)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | exact superpose eq362108 eq304778
    | (have j0 := eq304778 X0 x
       have j1 := eq362108 X0
       grind)
    | exact resolve eq304778 eq362108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304778 eq362108
  have eq602508 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x y)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq602365 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602365
  have eq602743 : ∀ X0 : G, (k X0 (M.op x y)) ≠ X0 ∨ (k X0 (M.op x y)) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq602508 X0
       grind)
    | exact superpose eq602508 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq602508 X0
       grind)
    | exact resolve eq12 eq602508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq602745 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 X0) ∨ (k X0 (M.op x y)) = X0 ∨ (k X0 (M.op x y)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0
       have i₂ := eq602508 X0
       grind)
    | exact superpose eq602508 eq14
    | (have j0 := eq14 X0 X0
       have j1 := eq602508 X0
       grind)
    | exact resolve eq14 eq602508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602508
  have eq603156 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 X0) ∨ (k X0 (M.op x y)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq602745 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602745
  have eq603385 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq603156 X0
       have j1 := eq370138 X0
       grind)
    | (have r₁ := eq603156 X0
       have r₂ := eq370138 X0
       grind)
    | (have r₁ := eq603156 (M.op x y)
       have r₂ := eq370138 (M.op x y)
       grind)
    | exact resolve eq603156 eq370138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603156
  have eq603386 : ∀ X0 : G, (k X0 (M.op x y)) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq602743 X0
       have j1 := eq370138 X0
       grind)
    | (have r₁ := eq602743 X0
       have r₂ := eq370138 X0
       grind)
    | (have r₁ := eq602743 (M.op x y)
       have r₂ := eq370138 (M.op x y)
       grind)
    | exact resolve eq602743 eq370138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370138 eq602743
  have eq603600 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq603386 X0
       have j1 := eq603385 X0
       grind)
    | (have r₁ := eq603386 X0
       have r₂ := eq603385 X0
       grind)
    | exact resolve eq603386 eq603385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603385 eq603386
  have eq604443 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq603600 X0
       grind)
    | exact superpose eq603600 eq9
    | exact resolve eq9 eq603600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604489 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq447 X0 X1 X0
       have i₂ := eq603600 X0
       grind)
    | exact superpose eq603600 eq447
    | exact resolve eq447 eq603600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604537 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (k X0 X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq996 X0 X0
       have i₂ := eq603600 X0
       grind)
    | exact superpose eq603600 eq996
    | exact resolve eq996 eq603600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq604586 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) (M.op X0 X1)) = (M.op (k (M.op X0 X1) (M.op X0 X1)) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq446 X0 X1 (M.op X0 X1) x
       have i₂ := eq603600 (M.op X0 X1)
       grind)
    | exact superpose eq603600 eq446
    | exact resolve eq446 eq603600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq604609 : (k (τ (σ x)) (τ (σ x))) = (M.op (k (τ (σ x)) (τ (σ x))) (M.op x y)) := by
    first
    | (have i₁ := eq444 (τ sF4)
       have i₂ := eq603600 (τ sF4)
       grind)
    | exact superpose eq603600 eq444
    | exact resolve eq444 eq603600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq604686 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = (k (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) ∨ (M.op X0 (M.op X0 X1)) = X0 ∨ (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq369 X0 X0 X1 (M.op X0 X1)
       have i₂ := eq603600 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq603600 eq369
    | (have j0 := eq369 X0 X0 X1 x
       grind)
    | exact resolve eq369 eq603600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq604688 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) ≠ X0 ∨ (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq427 X0 (M.op X0 X1) X0 X1
       have i₂ := eq603600 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq603600 eq427
    | (have j0 := eq427 X0 X1 X0 X1
       grind)
    | exact resolve eq427 eq603600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq604768 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (k (M.op X0 X1) (M.op X0 X1)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq807 X0 X1 (M.op X0 X1) X2
       have i₂ := eq603600 (M.op X0 X1)
       grind)
    | exact superpose eq603600 eq807
    | exact resolve eq807 eq603600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq604798 : (M.op (M.op x y) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq565 (τ sF4)
       have i₂ := eq603600 (τ sF4)
       grind)
    | exact superpose eq603600 eq565
    | exact resolve eq565 eq603600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq604983 : (M.op (σ y) (σ x)) = (M.op (k (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq69 sF5
       have i₂ := eq603600 sF5
       grind)
    | exact superpose eq603600 eq69
    | exact resolve eq69 eq603600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq605081 : (M.op (σ y) (σ x)) = (M.op (k (σ y) (σ y)) (σ x)) := by
    first
    | exact superpose eq3715 eq604983
    | exact resolve eq604983 eq3715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3715 eq604983
  have eq605181 : (M.op (M.op x y) (M.op x y)) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq518 eq604798
    | exact resolve eq604798 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518 eq604798
  have eq605208 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (k (M.op X0 X1) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq604768 X0 X1 X2
       have i₂ := eq3142 (k (M.op X0 X1) (M.op X0 X1)) X2 X0
       grind)
    | exact superpose eq3142 eq604768
    | exact resolve eq604768 eq3142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604768
  have eq605282 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op X0 X0)) ≠ X0 ∨ (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq604688 X1 x
       have i₂ := eq3142 X1 X1 x
       grind)
    | exact superpose eq3142 eq604688
    | (have j0 := eq604688 X0 X1
       grind)
    | exact resolve eq604688 eq3142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604688
  have eq605284 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op X0 X0)) = (k X0 (M.op X0 X1)) ∨ (M.op X0 (M.op X0 X1)) = X0 ∨ (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq604686 X1 x
       have i₂ := eq3142 X1 X1 x
       grind)
    | exact superpose eq3142 eq604686
    | (have j0 := eq604686 X0 X1
       grind)
    | exact resolve eq604686 eq3142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604686
  have eq605348 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X1)) = (M.op (k (M.op X0 X1) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq604586 X0 X1 x
       have i₂ := eq3142 (k (M.op X0 X1) (M.op X0 X1)) X0 x
       grind)
    | exact superpose eq3142 eq604586
    | exact resolve eq604586 eq3142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604586
  have eq605423 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq604489 X0 X1
       have i₂ := eq3041 X1 (k X0 X0) X0
       grind)
    | exact superpose eq3041 eq604489
    | exact resolve eq604489 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604489
  have eq605467 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq604443 X0 X1
       have i₂ := eq3142 (k X0 X0) X1 X0
       grind)
    | exact superpose eq3142 eq604443
    | exact resolve eq604443 eq3142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604443
  have eq605601 : (k (M.op x y) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq641 eq605181
    | exact resolve eq605181 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641 eq605181
  have eq605680 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq605282 X0 X1
       have i₂ := eq1525 X0 X0
       grind)
    | exact superpose eq1525 eq605282
    | (have j0 := eq605282 X0 X1
       grind)
    | exact resolve eq605282 eq1525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605282
  have eq605682 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X0 X1)) ∨ (M.op X0 (M.op X0 X1)) = X0 ∨ (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq605284 X0 X1
       have i₂ := eq1525 X0 X0
       grind)
    | exact superpose eq1525 eq605284
    | (have j0 := eq605284 X0 X1
       grind)
    | exact resolve eq605284 eq1525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1525 eq605284
  have eq605721 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq605348 X0 X1
       have i₂ := eq605208 X0 X1 X0
       grind)
    | exact superpose eq605208 eq605348
    | exact resolve eq605348 eq605208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605208 eq605348
  have eq605889 : (k (M.op x y) (M.op x y)) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq928 eq605601
    | exact resolve eq605601 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928 eq605601
  have eq605924 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq605680 X0 X1
       have i₂ := eq603600 X0
       grind)
    | exact superpose eq603600 eq605680
    | (have j0 := eq605680 X0 X1
       grind)
    | exact resolve eq605680 eq603600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605680
  have eq605926 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X0 X1)) ∨ (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq605682 X0 X1
       have j1 := eq13 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq605682 X0 X1
       have r₂ := eq13 X0 (M.op X0 X1)
       grind)
    | exact resolve eq605682 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605682
  have eq605946 : ∀ X0 X1 : G, (k X0 X0) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq605721 X0 X1
       have i₂ := eq603600 X0
       grind)
    | exact superpose eq603600 eq605721
    | exact resolve eq605721 eq603600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605721
  have eq606072 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X0 X1)) ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq605924 X0 X1
       have i₂ := eq3142 X0 X0 X1
       grind)
    | exact superpose eq3142 eq605924
    | (have j0 := eq605924 X0 X1
       grind)
    | exact resolve eq605924 eq3142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605924
  have eq606073 : ∀ X0 X1 : G, (k X0 X0) = (k X0 (M.op X0 X1)) ∨ (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq605926 X0 X1
       have i₂ := eq603600 X0
       grind)
    | exact superpose eq603600 eq605926
    | (have j0 := eq605926 X0 X1
       grind)
    | exact resolve eq605926 eq603600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605926
  have eq606147 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq606072 X0 X1
       have i₂ := eq603600 X0
       grind)
    | exact superpose eq603600 eq606072
    | (have j0 := eq606072 X0 X1
       grind)
    | exact resolve eq606072 eq603600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606072
  have eq606148 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq606073 X0 X1
       have i₂ := eq3041 X0 X0 X1
       grind)
    | exact superpose eq3041 eq606073
    | (have j0 := eq606073 X0 X1
       grind)
    | exact resolve eq606073 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3041 eq606073
  have eq606177 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X0 X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq606148 X0 X1
       have i₂ := eq603600 X0
       grind)
    | exact superpose eq603600 eq606148
    | (have j0 := eq606148 X0 X1
       grind)
    | exact resolve eq606148 eq603600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603600 eq606148
  have eq606186 : ∀ X0 X1 : G, (k X0 X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq606177 X0 X1
       have j1 := eq606147 X0 X1
       grind)
    | (have r₁ := eq606177 X0 X1
       have r₂ := eq606147 X0 X1
       grind)
    | exact resolve eq606177 eq606147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606147 eq606177
  have eq606208 : (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) = (M.op (k (τ (σ x)) (τ (σ x))) (M.op x y)) := by
    first
    | exact superpose eq486000 eq604537
    | exact resolve eq604537 eq486000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486000 eq604537
  have eq606603 : (k (τ (σ x)) (τ (σ x))) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | exact superpose eq604609 eq606208
    | exact resolve eq606208 eq604609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604609 eq606208
  have eq606709 : (k (M.op x y) (M.op x y)) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | exact superpose eq605889 eq606603
    | exact resolve eq606603 eq605889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606603
  have eq607425 : (k (σ x) (σ x)) = (M.op (σ x) (σ (k (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq606709 eq508299
    | exact resolve eq508299 eq606709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508299 eq606709
  have eq607694 : (k (σ x) (σ x)) = (M.op (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq607425
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq607425
    | exact resolve eq607425 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607425
  have eq607802 : (k (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq607694
       have i₂ := eq605423 (σ sF2) sF4
       grind)
    | exact superpose eq605423 eq607694
    | exact resolve eq607694 eq605423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607694
  have eq607891 : (M.op (σ x) (σ (M.op x y))) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq607802
    | exact resolve eq607802 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607802
  have eq617231 : (σ (k (M.op x y) (M.op x y))) = (k (σ (τ (σ x))) (σ (τ (σ x)))) := by
    first
    | exact superpose eq605889 eq15
    | exact resolve eq15 eq605889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605889
  have eq617255 : (σ (k (M.op x y) (M.op x y))) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq617231
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq617231
    | exact resolve eq617231 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617231
  have eq617277 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq617255
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq617255
    | exact resolve eq617255 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617255
  have eq617290 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq617277
    | exact resolve eq617277 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617277
  have eq617425 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (k (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq617290 eq605423
    | exact resolve eq605423 eq617290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq617426 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op (k (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq617290 eq605467
    | exact resolve eq605467 eq617290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617290
  have eq617496 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq485673 eq617426
    | exact resolve eq617426 eq485673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485673 eq617426
  have eq617497 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq486817 eq617425
    | exact resolve eq617425 eq486817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486817 eq617425
  have eq619203 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq617497 eq14
    | (have j0 := eq14 (σ (M.op x y)) X0
       grind)
    | exact resolve eq14 eq617497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617497
  have eq619761 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq617496 eq619203
    | (have j0 := eq619203 X0
       grind)
    | exact resolve eq619203 eq617496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619203
  have eq620364 : ∀ X0 : G, (k (M.op (σ y) X0) (M.op (σ y) X0)) = (k (M.op (σ y) X0) (M.op (σ y) (σ x))) := by
    intro X0
    first
    | exact superpose eq69 eq606186
    | exact resolve eq606186 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq606186
  have eq620772 : ∀ X0 : G, (k (σ y) (σ y)) = (k (M.op (σ y) X0) (M.op (σ y) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq620364 x
       have i₂ := eq605946 sF5 x
       grind)
    | exact superpose eq605946 eq620364
    | exact resolve eq620364 eq605946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620364
  have eq639986 : ∀ X0 X1 : G, (τ (k X0 X0)) = (k (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq125 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq605946 X0 X1
       grind)
    | exact superpose eq605946 eq125
    | exact resolve eq125 eq605946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605946
  have eq639992 : ∀ X0 X1 : G, (k (τ X0) (τ X0)) = (k (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq639986 X0 X1
       have i₂ := eq125 X0 X0
       grind)
    | exact superpose eq125 eq639986
    | exact resolve eq639986 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq639986
  have eq733291 : ∀ X0 X1 X2 : G, (M.op X1 (τ (M.op X0 X2))) = (M.op X1 (k (τ X0) (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq605423 (τ (M.op X0 X2)) X1
       have i₂ := eq639992 X0 X2
       grind)
    | exact superpose eq639992 eq605423
    | exact resolve eq605423 eq639992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639992
  have eq733308 : ∀ X0 X1 X2 : G, (M.op X1 (τ (M.op X0 X2))) = (M.op X1 (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq733291 X0 X1 X2
       have i₂ := eq605423 (τ X0) X1
       grind)
    | exact superpose eq605423 eq733291
    | exact resolve eq733291 eq605423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733291
  have eq1332193 : (M.op (σ y) (σ x)) = (k (σ (M.op x y)) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (k (σ y) (σ y)) (σ x)) := by
    first
    | exact superpose eq619761 eq605081
    | (have j1 := eq619761 (k (σ y) (σ y))
       grind)
    | exact resolve eq605081 eq619761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1332440 : (k (σ y) (σ y)) = (k (k (σ (M.op x y)) (σ y)) (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq619761 eq620772
    | (have j1 := eq619761 (σ y)
       grind)
    | exact resolve eq620772 eq619761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620772
  have eq1332457 : ∀ X0 : G, (σ (M.op x y)) ≠ (k (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq619761 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1332601 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (k (σ (M.op x y)) (σ y)) (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq32 eq1332440
    | exact resolve eq1332440 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332440
  have eq1332800 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ (M.op x y)) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (k (σ y) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq1332193
       have i₂ := eq605423 sF5 sF4
       grind)
    | exact superpose eq605423 eq1332193
    | exact resolve eq1332193 eq605423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605423 eq1332193
  have eq1333000 : (k (σ y) (σ y)) = (k (k (σ (M.op x y)) (σ y)) (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq1332601
       have r₂ := eq33
       grind)
    | exact resolve eq1332601 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332601
  have eq1333151 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ (M.op x y)) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (k (σ y) (σ y)) (σ x)) := by
    first
    | exact superpose eq32 eq1332800
    | exact resolve eq1332800 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332800
  have eq1333294 : (M.op (σ y) (σ x)) = (k (σ (M.op x y)) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (k (σ y) (σ y)) (σ x)) := by
    first
    | (have r₁ := eq1333151
       have r₂ := eq33
       grind)
    | exact resolve eq1333151 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1333151
  have eq1333335 : (M.op (σ y) (σ x)) = (k (σ (M.op x y)) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq605081 eq1333294
    | exact resolve eq1333294 eq605081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605081 eq1333294
  have eq1334177 : (k (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq619761 eq1333335
    | (have j1 := eq619761 (σ y)
       grind)
    | exact resolve eq1333335 eq619761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619761
  have eq1334384 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq1333335
  have eq1334519 : (k (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | (have j1 := eq1332457 (σ y)
       grind)
    | (have r₁ := eq1334177
       have r₂ := eq1332457 (σ y)
       grind)
    | exact resolve eq1334177 eq1332457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332457 eq1334177
  have eq1334614 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq32 eq1334519
    | exact resolve eq1334519 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1334519
  have eq1334653 : (k (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq1334614
       have r₂ := eq33
       grind)
    | exact resolve eq1334614 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334614
  have eq1336015 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1334653 eq1334384
    | exact resolve eq1334384 eq1334653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334384 eq1334653
  have eq1336021 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq1336015
  have eq1337718 : ∀ X0 : G, (M.op (k (σ (M.op x y)) (σ y)) X0) = (M.op (k (σ y) (σ y)) X0) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq1333000 eq605467
    | exact resolve eq605467 eq1333000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1333000
  have eq1337749 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (k (σ (M.op x y)) (σ y)) X0) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1337718 x
       have i₂ := eq605467 sF5 x
       grind)
    | exact superpose eq605467 eq1337718
    | exact resolve eq1337718 eq605467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605467 eq1337718
  have eq1338854 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (σ y) X0))) = (M.op X1 (τ (k (σ (M.op x y)) (σ y)))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f1338854_13 : ∀ X0 X1 X2 : G, (M.op X1 (τ (M.op X0 X2))) = (M.op X1 (τ X0)) := by
      intro X0 X1 X2
      grind
    have f1338854_14 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (k (σ (M.op x y)) (σ y)) X0) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
      intro X0
      grind
    have f1338854_16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
      intro X0
      grind
    have f1338854_17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
      intro X0
      grind
    have f1338854_21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
      intro X0 X1
      grind
    have f1338854_23 : (M.op X1 (τ (M.op (σ y) X0))) ≠ (M.op X1 (τ (k (σ (M.op x y)) (σ y)))) := by grind
    have f1338854_24 : (σ (M.op x y)) ≠ (M.op (σ y) (σ x)) := by grind
    have f1338854_25 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (k (σ (M.op x y)) (σ y)) X0) := by
      intro X0
      first
      | (have j0 := f1338854_14 X0
         grind)
      | (have r₁ := f1338854_14 X0
         have r₂ := f1338854_24
         grind)
      | exact resolve f1338854_14 f1338854_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1338854_26 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (k (M.op x y) y)) X0) := by
      intro X0
      first
      | (have i₁ := f1338854_25 X0
         have i₂ := f1338854_21 (M.op x y) y
         grind)
      | exact superpose f1338854_21 f1338854_25
      | exact resolve f1338854_25 f1338854_21
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1338854_27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
      intro X0 X1
      first
      | (have i₁ := f1338854_21 (τ X0) X1
         have i₂ := f1338854_17 X0
         grind)
      | exact superpose f1338854_17 f1338854_21
      | exact resolve f1338854_21 f1338854_17
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1338854_33 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
      intro X0 X1
      first
      | (have i₁ := f1338854_16 (k (τ X0) X1)
         have i₂ := f1338854_27 X0 X1
         grind)
      | exact superpose f1338854_27 f1338854_16
      | exact resolve f1338854_16 f1338854_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1338854_62 : ∀ X0 X1 : G, (M.op X1 (τ (σ (k (M.op x y) y)))) = (M.op X1 (τ (M.op (σ y) X0))) := by
      intro X0 X1
      first
      | (have i₁ := f1338854_13 (σ (k (M.op x y) y)) X1 X0
         have i₂ := f1338854_26 X0
         grind)
      | exact superpose f1338854_26 f1338854_13
      | exact resolve f1338854_13 f1338854_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1338854_65 : ∀ X1 : G, (M.op X1 (τ (σ (k (M.op x y) y)))) = (M.op X1 (τ (σ y))) := by
      intro X1
      first
      | (have i₁ := f1338854_62 x X1
         have i₂ := f1338854_13 (σ y) X1 x
         grind)
      | exact superpose f1338854_13 f1338854_62
      | exact resolve f1338854_62 f1338854_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1338854_69 : ∀ X1 : G, (M.op X1 (τ (σ (k (M.op x y) y)))) = (M.op X1 y) := by
      intro X1
      first
      | (have i₁ := f1338854_65 X1
         have i₂ := f1338854_16 y
         grind)
      | exact superpose f1338854_16 f1338854_65
      | exact resolve f1338854_65 f1338854_16
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1338854_70 : ∀ X1 : G, (M.op X1 y) = (M.op X1 (k (M.op x y) y)) := by
      intro X1
      first
      | (have i₁ := f1338854_69 X1
         have i₂ := f1338854_16 (k (M.op x y) y)
         grind)
      | exact superpose f1338854_16 f1338854_69
      | exact resolve f1338854_69 f1338854_16
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1338854_121 : (M.op X1 (τ (M.op (σ y) X0))) ≠ (M.op X1 (k (τ (σ (M.op x y))) y)) := by
      first
      | (have i₁ := f1338854_23
         have i₂ := f1338854_33 (σ (M.op x y)) y
         grind)
      | exact superpose f1338854_33 f1338854_23
      | exact resolve f1338854_23 f1338854_33
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1338854_122 : (M.op X1 (τ (M.op (σ y) X0))) ≠ (M.op X1 (k (M.op x y) y)) := by
      first
      | (have i₁ := f1338854_121
         have i₂ := f1338854_16 (M.op x y)
         grind)
      | exact superpose f1338854_16 f1338854_121
      | exact resolve f1338854_121 f1338854_16
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1338854_126 : (M.op X1 (τ (M.op (σ y) X0))) ≠ (M.op X1 y) := by
      first
      | (have i₁ := f1338854_122
         have i₂ := f1338854_70 X1
         grind)
      | exact superpose f1338854_70 f1338854_122
      | exact resolve f1338854_122 f1338854_70
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1338854_130 : (M.op X1 (τ (σ y))) ≠ (M.op X1 y) := by
      first
      | (have i₁ := f1338854_126
         have i₂ := f1338854_13 (σ y) X1 X0
         grind)
      | exact superpose f1338854_13 f1338854_126
      | exact resolve f1338854_126 f1338854_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1338854_133 : (M.op X1 y) ≠ (M.op X1 y) := by
      first
      | (have i₁ := f1338854_130
         have i₂ := f1338854_16 y
         grind)
      | exact superpose f1338854_16 f1338854_130
      | exact resolve f1338854_130 f1338854_16
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1338854_134 : False := by grind
    exact f1338854_134
  clear eq1337749
  have eq1339163 : ∀ X0 X1 : G, (M.op X1 (k (M.op x y) (τ (σ y)))) = (M.op X1 (τ (M.op (σ y) X0))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq73 eq1338854
    | exact resolve eq1338854 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq1338854
  have eq1339357 : ∀ X1 : G, (M.op X1 (k (M.op x y) (τ (σ y)))) = (M.op X1 (τ (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    intro X1
    first
    | (have i₁ := eq1339163 x X1
       have i₂ := eq733308 sF5 X1 x
       grind)
    | exact superpose eq733308 eq1339163
    | exact resolve eq1339163 eq733308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733308 eq1339163
  have eq1355284 : (k (M.op x y) (τ (σ y))) = (M.op (M.op x y) (τ (σ y))) ∨ (M.op x y) = (M.op (τ (σ y)) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1339357 eq26974
    | exact resolve eq26974 eq1339357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26974 eq1339357
  have eq1355588 : (k (M.op x y) (τ (σ y))) = (M.op (M.op x y) (τ (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | (have j1 := eq12 (M.op x y) (τ (σ y))
       grind)
    | (have r₁ := eq1355284
       have r₂ := eq12 (M.op x y) (τ (σ y))
       grind)
    | exact resolve eq1355284 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1355284
  have eq1355731 : (M.op x y) = (k (M.op x y) (τ (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq293 eq1355588
    | exact resolve eq1355588 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293 eq1355588
  have eq1357321 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (τ (σ y)))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1355731 eq15
    | exact resolve eq15 eq1355731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1355731
  have eq1357334 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1357321
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq1357321
    | exact resolve eq1357321 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1357321
  have eq1357337 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq1357334
    | exact resolve eq1357334 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1357334
  have eq1357340 : (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq1357337
       have r₂ := eq1336021
       grind)
    | exact resolve eq1357337 eq1336021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336021 eq1357337
  have eq1357421 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1357340 eq2833
    | exact resolve eq2833 eq1357340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2833
  have eq1357531 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq1357340 eq447
    | exact resolve eq447 eq1357340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447 eq1357340
  have eq1357991 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq617496 eq1357531
    | exact resolve eq1357531 eq617496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617496 eq1357531
  have eq1358083 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq3045 eq1357421
    | exact resolve eq1357421 eq3045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3045 eq1357421
  have eq1358254 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1357991 x
       have i₂ := eq3142 sF4 sF4 x
       grind)
    | exact superpose eq3142 eq1357991
    | exact resolve eq1357991 eq3142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3142 eq1357991
  have eq1358325 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq607891 eq1358083
    | exact resolve eq1358083 eq607891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607891 eq1358083
  have eq1358458 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq485801 eq1358254
    | exact resolve eq1358254 eq485801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485801 eq1358254
  have eq1362257 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) := by
    first
    | exact superpose eq1358325 eq33
    | exact resolve eq33 eq1358325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq1358325
  have eq1362916 : False := by grind
  exact eq1362916

/-- `Equation3744`: `x ◇ y = (x ◇ z) ◇ (w ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_x_y_pxy_Equation3744 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3744 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3744.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq10
    | exact resolve eq10 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22
    | exact resolve eq22 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 (k X0 (τ X1)) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq28
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq9 (M.op X0 X2) X3 (M.op x X1) X5
       have i₂ := eq9 X0 X1 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X2 (M.op X3 X1) X4 (M.op X0 x)
       have i₂ := eq9 X0 X1 x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq62 x X1 X2 X3 x
       have i₂ := eq9 X2 X1 x x
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq65 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq61 X0 x X2 X3 x
       have i₂ := eq9 X0 X3 x x
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq85 : ∀ X0 X1 X2 : G, (k X1 (M.op X0 X2)) = X1 ∨ (M.op X0 X1) ≠ (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (M.op X0 X2)
       have i₂ := eq65 X0 X2 X1
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X1 (M.op X0 X2)
       grind)
    | (have r₁ := eq12 x (M.op X0 x)
       have r₂ := eq65 X0 x x
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X2))) ∨ (M.op X1 X2) ≠ (M.op X1 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X0 (M.op X1 X2)
       have i₂ := eq85 X1 (σ X0) X2
       grind)
    | exact superpose eq85 eq28
    | (have j1 := eq85 X1 X2 (σ X0)
       grind)
    | exact resolve eq28 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X2))) ∨ (M.op X1 X2) ≠ (M.op X1 (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (M.op X1 X2)
       have i₂ := eq85 X1 (τ X0) X2
       grind)
    | exact superpose eq85 eq17
    | (have j1 := eq85 X1 X2 (τ X0)
       grind)
    | exact resolve eq17 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (M.op X1 (τ X0)) ∨ (k X0 (σ (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq101 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq101
    | (have j0 := eq101 X0 X1 X2
       grind)
    | exact resolve eq101 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq103 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (M.op X1 (σ X0)) ∨ (k X0 (τ (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq100 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq100
    | (have j0 := eq100 X0 X1 X2
       grind)
    | exact resolve eq100 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq335 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1 (τ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (M.op X1 (τ (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 (M.op X1 (τ (σ X0)))
       have i₂ := eq335 (σ X0) X1
       grind)
    | exact superpose eq335 eq15
    | exact resolve eq15 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq364 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op X1 (τ (σ X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ (M.op X1 (τ (σ X0))))
       have i₂ := eq335 (σ X0) X1
       grind)
    | exact superpose eq335 eq28
    | exact resolve eq28 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 (τ (τ X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (M.op X1 (τ (τ X0))))
       have i₂ := eq335 (τ X0) X1
       grind)
    | exact superpose eq335 eq17
    | exact resolve eq17 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op X1 (τ (τ X0)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq365 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq365
    | exact resolve eq365 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq375 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq364 X0 X1
       have i₂ := eq10 (M.op X1 (τ (σ X0)))
       grind)
    | exact superpose eq10 eq364
    | exact resolve eq364 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq380 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq359 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq359
    | exact resolve eq359 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq393 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq375 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq375
    | exact resolve eq375 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq403 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k (M.op X2 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq393 (M.op X2 X1) X0
       have i₂ := eq64 X1 X0 X2
       grind)
    | exact superpose eq64 eq393
    | exact resolve eq393 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq409 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op X1 (σ X0))
       have i₂ := eq393 (σ X0) X1
       grind)
    | exact superpose eq393 eq28
    | exact resolve eq28 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq416 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq409 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq409
    | exact resolve eq409 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq676 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq677 : ∀ X0 X1 X2 : G, (M.op X2 X0) = X2 ∨ (M.op X1 X0) = (M.op X1 X2) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X2 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq64
    | (have j1 := eq14 X2 X0
       grind)
    | exact resolve eq64 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq393 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq393
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq393 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq696 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq699 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq676 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq700 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq699 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq730 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq697 (σ X0)
       grind)
    | exact superpose eq697 eq15
    | (have j1 := eq697 (σ X0)
       grind)
    | exact resolve eq15 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq737 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq697 (τ X0)
       grind)
    | exact superpose eq697 eq17
    | (have j1 := eq697 (τ X0)
       grind)
    | exact resolve eq17 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq746 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq737 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq737
    | (have j0 := eq737 X0
       grind)
    | exact resolve eq737 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq989 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X1 X0) = X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq393 X1 X0
       have i₂ := eq700 X1 X0
       grind)
    | exact superpose eq700 eq393
    | (have j1 := eq700 X1 X0
       grind)
    | exact resolve eq393 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq1426 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq682 X1 X0
       grind)
    | exact superpose eq682 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq682 X1 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq682 X0 X1
       grind)
    | exact resolve eq13 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq1462 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1426 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426
  have eq1468 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1462 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq1462 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1462 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1462
  have eq1777 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1468 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468
  have eq1998 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 (σ X0)) = (M.op X1 (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (σ X0) X1 (σ X0)
       have i₂ := eq730 X0
       grind)
    | exact superpose eq730 eq64
    | (have j1 := eq730 X0
       grind)
    | exact resolve eq64 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2018 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq730 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq2071 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2018 (M.op X0 X1)
       have i₂ := eq403 X0 X1 X0
       grind)
    | exact superpose eq403 eq2018
    | (have j0 := eq2018 (M.op X0 X1)
       grind)
    | exact resolve eq2018 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2075 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2018 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq2018
    | (have j0 := eq2018 (τ X0)
       grind)
    | exact resolve eq2018 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2018
  have eq2076 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq2071 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2071
  have eq2081 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2075 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2075
    | (have j0 := eq2075 X0
       grind)
    | exact resolve eq2075 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2075
  have eq2084 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2081 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2081
    | (have j0 := eq2081 X0
       grind)
    | exact resolve eq2081 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2081
  have eq2095 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2084 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq2084
    | (have j0 := eq2084 (τ X0)
       grind)
    | exact resolve eq2084 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084
  have eq2160 : ∀ X0 X1 : G, (τ (M.op X0 X1)) ≠ (τ (M.op X0 X1)) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2095 (M.op X0 X1)
       have i₂ := eq403 X0 X1 X0
       grind)
    | exact superpose eq403 eq2095
    | (have j0 := eq2095 (M.op X0 X1)
       grind)
    | exact resolve eq2095 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq2169 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq2160 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2160
  have eq2986 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq746 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq746
    | exact resolve eq746 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq3034 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2986 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq2986
    | (have j0 := eq2986 X0
       grind)
    | exact resolve eq2986 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2986
  have eq3072 : ∀ X0 X1 : G, (k (k X0 X0) (τ X1)) = (τ (k (σ (M.op X0 X0)) X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 (k X0 X0) X1
       have i₂ := eq3034 X0
       grind)
    | exact superpose eq3034 eq28
    | (have j1 := eq3034 X0
       grind)
    | exact resolve eq28 eq3034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3034
  have eq3090 : ∀ X0 X1 : G, (k (k X0 X0) (τ X1)) = (k (M.op X0 X0) (τ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3072 X0 X1
       have i₂ := eq28 (M.op X0 X0) X1
       grind)
    | exact superpose eq28 eq3072
    | (have j0 := eq3072 X0 X1
       grind)
    | exact resolve eq3072 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3072
  have eq3340 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k (k X1 X1) X0) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3090 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3090
    | (have j0 := eq3090 X1 X1
       grind)
    | exact resolve eq3090 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3090
  have eq3418 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (k X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2076 X1 X1
       have i₂ := eq3340 X0 X1
       grind)
    | exact superpose eq3340 eq2076
    | (have j1 := eq3340 X0 (σ X0)
       grind)
    | exact resolve eq2076 eq3340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3340
  have eq13573 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq677 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23524 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (M.op X1 (σ (k (τ X0) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1998 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1998
    | exact resolve eq1998 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23551 : ∀ X0 X1 : G, (k X0 (τ (σ X0))) = X0 ∨ (M.op X1 (σ X0)) = (M.op X1 (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq416 X0 (σ X0)
       have i₂ := eq1998 X0 X1
       grind)
    | exact superpose eq1998 eq416
    | (have j1 := eq1998 X0 X1
       grind)
    | exact resolve eq416 eq1998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1998
  have eq23618 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 (σ X0)) = (M.op X1 (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23551 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23551
    | (have j0 := eq23551 X0 X1
       grind)
    | exact resolve eq23551 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23551
  have eq23624 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k (σ (τ X0)) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23524 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq23524
    | (have j0 := eq23524 X0 X1
       grind)
    | exact resolve eq23524 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23524
  have eq23635 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (M.op X1 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23624 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23624
    | (have j0 := eq23624 X0 X1
       grind)
    | exact resolve eq23624 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23624
  have eq23671 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op X1 X0) = (M.op X1 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq380 X0 X0
       have i₂ := eq23635 X0 X1
       grind)
    | exact superpose eq23635 eq380
    | (have j1 := eq23635 X0 X1
       grind)
    | exact resolve eq380 eq23635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380 eq23635
  have eq24561 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 (σ X0)) = (M.op X1 (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23618 X0 X1
       have i₂ := eq697 X0
       grind)
    | exact superpose eq697 eq23618
    | (have j1 := eq697 X0
       grind)
    | exact resolve eq23618 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23618
  have eq24676 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 (σ X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq24561 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24561
  have eq38779 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X2) ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13573 (M.op x X1) X1
       have i₂ := eq9 x X1 X1 x
       grind)
    | exact superpose eq9 eq13573
    | (have j0 := eq13573 (M.op X0 X1) X2
       grind)
    | (have r₁ := eq13573 (M.op x X1) X1
       have r₂ := eq9 x X1 X1 x
       grind)
    | exact resolve eq13573 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13573
  have eq38807 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X2) ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq38779 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38779
  have eq38870 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38807 X0 X1 X2
       have i₂ := eq65 X0 X1 X2
       grind)
    | exact superpose eq65 eq38807
    | (have j0 := eq38807 X0 X1 X2
       grind)
    | exact resolve eq38807 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38807
  have eq38874 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k (M.op X0 X1) X2) ∨ (M.op X0 X1) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38870 X0 X1 X2
       have i₂ := eq65 X0 X1 X2
       grind)
    | exact superpose eq65 eq38870
    | (have j0 := eq38870 X0 X1 X2
       grind)
    | exact resolve eq38870 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38870
  have eq39232 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X1 X2)) ∨ (M.op X1 X2) ≠ (M.op X1 (M.op X0 X3)) ∨ (M.op X0 X3) = (M.op X0 (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq85 X1 (M.op X0 X3) X2
       have i₂ := eq38874 X0 X3 (M.op X1 X2)
       grind)
    | exact superpose eq38874 eq85
    | (have j0 := eq85 X1 X2 (M.op X0 X3)
       have j1 := eq38874 X0 X3 (M.op X1 X2)
       grind)
    | (have r₁ := eq85 X0 X1 X2
       have r₂ := eq38874 X0 X1 X2
       grind)
    | (have r₁ := eq85 X0 X2 X1
       have r₂ := eq38874 X0 X1 X2
       grind)
    | exact resolve eq85 eq38874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq39247 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (σ (M.op X1 (τ (M.op X0 X2))))) ∨ (M.op X0 X2) = (M.op X0 (σ (M.op X1 (τ (M.op X0 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq335 (M.op X0 X2) X1
       have i₂ := eq38874 X0 X2 (σ (M.op X1 (τ (M.op X0 X2))))
       grind)
    | exact superpose eq38874 eq335
    | (have j1 := eq38874 X0 X2 (σ (M.op X1 (τ (M.op X0 X2))))
       grind)
    | exact resolve eq335 eq38874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39248 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (σ (σ (M.op X1 (τ (τ (M.op X0 X2))))))) ∨ (M.op X0 X2) = (M.op X0 (σ (σ (M.op X1 (τ (τ (M.op X0 X2))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq374 (M.op X0 X2) X1
       have i₂ := eq38874 X0 X2 (σ (σ (M.op X1 (τ (τ (M.op X0 X2))))))
       grind)
    | exact superpose eq38874 eq374
    | (have j1 := eq38874 X0 X2 (σ (σ (M.op X1 (τ (τ (M.op X0 X2))))))
       grind)
    | exact resolve eq374 eq38874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39257 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (τ (M.op X1 (σ (M.op X0 X2))))) ∨ (M.op X0 X2) = (M.op X0 (τ (M.op X1 (σ (M.op X0 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq416 (M.op X0 X2) X1
       have i₂ := eq38874 X0 X2 (τ (M.op X1 (σ (M.op X0 X2))))
       grind)
    | exact superpose eq38874 eq416
    | (have j1 := eq38874 X0 X2 (τ (M.op X1 (σ (M.op X0 X2))))
       grind)
    | exact resolve eq416 eq38874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38874
  have eq39308 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (τ (M.op X1 (σ (M.op X0 X2))))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq39257 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39257
  have eq39312 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (σ (σ (M.op X1 (τ (τ (M.op X0 X2))))))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq39248 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39248
  have eq39313 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (σ (M.op X1 (τ (M.op X0 X2))))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq39247 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39247
  have eq39318 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X1 X2)) ∨ (M.op X1 X2) ≠ (M.op X1 (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq39232 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39232
  have eq39469 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) = (M.op X0 X3) ∨ (M.op X1 X2) ≠ (M.op X1 (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq39318 X0 X1 X2 X3
       have i₂ := eq64 X2 X0 X1
       grind)
    | exact superpose eq64 eq39318
    | (have j0 := eq39318 X0 X1 X2 X3
       grind)
    | (have r₁ := eq39318 X0 X2 (M.op X3 (M.op X0 X3)) X3
       have r₂ := eq64 (M.op X0 X3) X2 X3
       grind)
    | (have r₁ := eq39318 X3 X2 X1 X1
       have r₂ := eq64 X1 X2 X3
       grind)
    | exact resolve eq39318 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39318
  have eq39481 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) ≠ (M.op X1 X3) ∨ (M.op X0 X2) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq39469 X0 X1 X2 X3
       have i₂ := eq64 X3 X1 X0
       grind)
    | exact superpose eq64 eq39469
    | (have j0 := eq39469 X0 X1 X2 X3
       grind)
    | (have r₁ := eq39469 X0 X2 (M.op X3 (M.op X0 X3)) X3
       have r₂ := eq64 (M.op X0 X3) X2 X3
       grind)
    | (have r₁ := eq39469 X3 X2 X1 X1
       have r₂ := eq64 X1 X2 X3
       grind)
    | exact resolve eq39469 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39469
  have eq39558 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X2 (τ (σ (M.op X0 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39313 (σ (M.op X0 X1)) X1 (σ (M.op X0 X1))
       have i₂ := eq2076 X0 X1
       grind)
    | exact superpose eq2076 eq39313
    | exact resolve eq39313 eq2076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39667 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 (σ (M.op X3 (τ (M.op X0 X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64 (σ (M.op X3 (τ (M.op X0 X1)))) X2 X0
       have i₂ := eq39313 X0 X3 X1
       grind)
    | exact superpose eq39313 eq64
    | exact resolve eq64 eq39313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39313
  have eq39730 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (σ (M.op X3 (τ (M.op X0 X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq39667 X0 X1 X2 X3
       have i₂ := eq64 X1 X2 X0
       grind)
    | exact superpose eq64 eq39667
    | exact resolve eq39667 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39667
  have eq39798 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39558 X0 X1 X2
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq39558
    | exact resolve eq39558 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39558
  have eq39811 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39798 X0 X1 X2
       have i₂ := eq64 X1 X2 X0
       grind)
    | exact superpose eq64 eq39798
    | exact resolve eq39798 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39798
  have eq39886 : ∀ X0 X1 X2 X3 : G, (M.op X2 (σ (M.op X0 X1))) = (M.op X2 (σ (M.op X3 (τ (σ (M.op X0 X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq39730 (σ (M.op X0 X1)) (σ (M.op X0 X1)) X2 X3
       have i₂ := eq2076 X0 X1
       grind)
    | exact superpose eq2076 eq39730
    | exact resolve eq39730 eq2076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40195 : ∀ X0 X1 X2 : G, (σ (M.op X0 (τ (M.op X1 X2)))) = (M.op (σ (M.op X0 (τ (M.op X1 X2)))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2076 X0 (τ (M.op X1 X2))
       have i₂ := eq39730 X1 X2 (σ (M.op X0 (τ (M.op X1 X2)))) X0
       grind)
    | exact superpose eq39730 eq2076
    | exact resolve eq2076 eq39730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2076
  have eq40293 : ∀ X0 X1 X2 X3 : G, (M.op X2 (σ (M.op X0 X1))) = (M.op X2 (σ (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq39886 X0 X1 X2 X3
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq39886
    | exact resolve eq39886 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39886
  have eq40317 : ∀ X0 X1 X2 X3 : G, (M.op X2 (σ (M.op X0 X1))) = (M.op X2 (σ (M.op X3 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq40293 X0 X1 X2 X3
       have i₂ := eq64 X1 X3 X0
       grind)
    | exact superpose eq64 eq40293
    | exact resolve eq40293 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq40293
  have eq40421 : ∀ X0 X1 X2 X3 : G, (M.op X2 (τ (M.op X0 X1))) = (M.op X2 (τ (M.op X3 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq39308 X2 X3 (τ (M.op X0 X1))
       have i₂ := eq39730 X0 X1 X3 X2
       grind)
    | exact superpose eq39730 eq39308
    | exact resolve eq39308 eq39730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40569 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (σ (M.op X4 (τ (M.op X0 X1))))) = (M.op X2 (τ (M.op X3 (σ (M.op X0 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq39730 X0 (τ (M.op X3 (σ (M.op X0 X1)))) X2 X4
       have i₂ := eq39308 X0 X3 X1
       grind)
    | exact superpose eq39308 eq39730
    | exact resolve eq39730 eq39308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39308
  have eq40572 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (τ (M.op X3 (σ (M.op X0 X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq40569 X0 X1 X2 X3 x
       have i₂ := eq39730 X0 X1 X2 x
       grind)
    | exact superpose eq39730 eq40569
    | exact resolve eq40569 eq39730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40569
  have eq41644 : ∀ X0 X1 X2 X3 : G, (M.op X2 (τ (τ (M.op X0 X1)))) = (M.op X2 (τ (M.op X3 (τ (M.op X0 X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq40421 X3 (τ (M.op X0 X1)) X2 (τ (M.op X0 X1))
       have i₂ := eq2169 X0 X1
       grind)
    | exact superpose eq2169 eq40421
    | exact resolve eq40421 eq2169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43026 : ∀ X0 X1 X2 : G, (σ (M.op X1 X0)) = (M.op (σ (M.op X1 X0)) (σ X0)) ∨ (M.op X2 (σ X0)) = (M.op X2 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39811 X1 X0 X0
       have i₂ := eq24676 X0 X2
       grind)
    | exact superpose eq24676 eq39811
    | (have j1 := eq24676 X0 X2
       grind)
    | exact resolve eq39811 eq24676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24676
  have eq43159 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op X0 X1)) ≠ (M.op (σ (M.op X0 X1)) X2) ∨ (M.op X4 X2) = (M.op X4 (σ (M.op X3 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq39481 X4 (σ (M.op X0 X1)) X2 (σ (M.op X3 X1))
       have i₂ := eq39811 X0 X1 X3
       grind)
    | exact superpose eq39811 eq39481
    | (have j0 := eq39481 X4 X1 X2 (σ (M.op X3 X1))
       grind)
    | exact resolve eq39481 eq39811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43220 : ∀ X0 X2 : G, (M.op X2 (σ X0)) = (M.op X2 (σ (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have j0 := eq43026 X0 x X2
       have j1 := eq43159 X0 X0 (σ X0) X0 X2
       grind)
    | (have r₁ := eq43026 x X0 X2
       have r₂ := eq43159 X0 x (σ x) x x
       grind)
    | exact resolve eq43026 eq43159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43026 eq43159
  have eq43355 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (τ (M.op X0 (σ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40572 X1 X1 X2 X0
       have i₂ := eq43220 X1 X0
       grind)
    | exact superpose eq43220 eq40572
    | exact resolve eq40572 eq43220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43357 : ∀ X0 X1 X2 : G, (M.op X0 (σ X1)) = (M.op X0 (σ (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40317 X1 X1 X0 X2
       have i₂ := eq43220 X1 X0
       grind)
    | exact superpose eq43220 eq40317
    | exact resolve eq40317 eq43220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40317
  have eq43608 : ∀ X0 X1 X2 : G, (M.op X1 (τ X0)) = (M.op X1 (τ (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43355 X2 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq43355
    | exact resolve eq43355 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43618 : ∀ X0 X1 X2 X3 : G, (M.op X1 (k X0 X0)) = (M.op X1 (τ (M.op X2 (σ X0)))) ∨ (M.op X3 X0) = (M.op X3 (k X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq43355 X2 (k X0 X0) X1
       have i₂ := eq23671 X0 X3
       grind)
    | exact superpose eq23671 eq43355
    | (have j1 := eq23671 X0 X3
       grind)
    | exact resolve eq43355 eq23671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23671
  have eq43964 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (τ (M.op X0 X1))) = (M.op X2 (τ (M.op X3 (τ (M.op X4 (σ X1)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq40421 X3 (τ (M.op X4 (σ X1))) X2 X0
       have i₂ := eq43355 X4 X1 X0
       grind)
    | exact superpose eq43355 eq40421
    | exact resolve eq40421 eq43355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40421
  have eq43971 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (M.op (τ (M.op X0 (σ X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2169 X0 (σ X1)
       have i₂ := eq43355 X0 X1 (τ (M.op X0 (σ X1)))
       grind)
    | exact superpose eq43355 eq2169
    | exact resolve eq2169 eq43355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2169
  have eq43980 : ∀ X0 X1 X2 X4 : G, (M.op X2 (τ (M.op X0 X1))) = (M.op X2 (τ (τ (M.op X4 (σ X1))))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq43964 X0 X1 X2 x X4
       have i₂ := eq41644 X4 (σ X1) X2 x
       grind)
    | exact superpose eq41644 eq43964
    | exact resolve eq43964 eq41644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41644 eq43964
  have eq44054 : ∀ X0 X1 X3 : G, (M.op X1 X0) = (M.op X1 (k X0 X0)) ∨ (M.op X3 X0) = (M.op X3 (k X0 X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq43618 X0 X1 x X3
       have i₂ := eq43355 x X0 X1
       grind)
    | exact superpose eq43355 eq43618
    | (have j0 := eq43618 X0 X1 x X1
       grind)
    | exact resolve eq43618 eq43355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43618
  have eq44071 : ∀ X1 X2 X4 : G, (M.op X2 (τ X1)) = (M.op X2 (τ (τ (M.op X4 (σ X1))))) := by
    intro X1 X2 X4
    first
    | (have i₁ := eq43980 x X1 X2 X4
       have i₂ := eq43608 X1 X2 x
       grind)
    | exact superpose eq43608 eq43980
    | exact resolve eq43980 eq43608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43980
  have eq44090 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq44054 X0 X1 X1
       have j1 := eq39481 X1 X1 X0 (k X0 X0)
       grind)
    | (have r₁ := eq44054 x X1 x
       have r₂ := eq39481 X0 X1 x (k x x)
       grind)
    | (have r₁ := eq44054 x X1 x
       have r₂ := eq39481 X0 X1 (k x x) x
       grind)
    | (have r₁ := eq44054 x X1 X1
       have r₂ := eq39481 X0 X1 x (k x x)
       grind)
    | exact resolve eq44054 eq39481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44054
  have eq44106 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq44090 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq44090
    | exact resolve eq44090 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44107 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (M.op X1 (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq44090 (τ X0) X1
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq44090
    | exact resolve eq44090 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44291 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X1) ∨ (k X0 (k X1 X1)) = X0 ∨ (k X1 X1) = (k X0 (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1777 X0 (k X1 X1)
       have i₂ := eq44090 X1 X0
       grind)
    | exact superpose eq44090 eq1777
    | (have j0 := eq1777 X0 (k X1 X1)
       grind)
    | exact resolve eq1777 eq44090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44630 : ∀ X0 X1 X2 : G, (M.op X2 (σ (σ (M.op X0 X1)))) = (M.op X2 (σ (M.op (σ (M.op X0 X1)) (σ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43220 (σ (M.op X0 X1)) X2
       have i₂ := eq43357 (σ (M.op X0 X1)) X1 X0
       grind)
    | exact superpose eq43357 eq43220
    | exact resolve eq43220 eq43357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43220
  have eq44747 : ∀ X0 X1 X2 : G, (M.op X2 (σ (σ (M.op X0 X1)))) = (M.op X2 (σ (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44630 X0 X1 X2
       have i₂ := eq43357 X2 (σ X1) (σ (M.op X0 X1))
       grind)
    | exact superpose eq43357 eq44630
    | exact resolve eq44630 eq43357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44630
  have eq45256 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k (M.op X2 X1) (σ (M.op X0 (τ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq335 (M.op X2 X1) X0
       have i₂ := eq43608 X1 X0 X2
       grind)
    | exact superpose eq43608 eq335
    | exact resolve eq335 eq43608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45398 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 (τ X1))) = (M.op (σ (M.op X0 (τ X1))) (σ (M.op X3 (τ (M.op X2 X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq39811 X1 (τ (M.op X2 X0)) X2
       have i₂ := eq43608 X0 X1 X2
       grind)
    | exact superpose eq43608 eq39811
    | exact resolve eq39811 eq43608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39811
  have eq45426 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (M.op (σ (M.op X0 (τ X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45398 X0 X1 x x
       have i₂ := eq39730 x X1 (σ (M.op X0 (τ X1))) x
       grind)
    | exact superpose eq39730 eq45398
    | exact resolve eq45398 eq39730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45398
  have eq46093 : ∀ X0 X1 : G, (M.op X1 (τ (τ X0))) = (M.op X1 (τ (τ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq44107 (τ X0) X1
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq44107
    | exact resolve eq44107 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44107
  have eq49980 : ∀ X0 X1 X2 X3 : G, (M.op X2 (τ (M.op X0 (τ X1)))) = (M.op X2 (τ (τ (τ (M.op X3 (σ X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq43608 (τ (τ (M.op X3 (σ X1)))) X2 X0
       have i₂ := eq44071 X1 X0 X3
       grind)
    | exact superpose eq44071 eq43608
    | exact resolve eq43608 eq44071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50004 : ∀ X1 X2 X3 : G, (M.op X2 (τ (τ X1))) = (M.op X2 (τ (τ (τ (M.op X3 (σ X1)))))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq49980 x X1 X2 X3
       have i₂ := eq43608 (τ X1) X2 x
       grind)
    | exact superpose eq43608 eq49980
    | exact resolve eq49980 eq43608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49980
  have eq51679 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 (τ X1))) ≠ (M.op (σ (M.op X0 (τ X1))) X2) ∨ (M.op X3 X1) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq39481 X3 (σ (M.op X0 (τ X1))) X2 X1
       have i₂ := eq45426 X0 X1
       grind)
    | exact superpose eq45426 eq39481
    | (have j0 := eq39481 X3 X1 X1 X2
       grind)
    | exact resolve eq39481 eq45426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51727 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k (M.op X2 X1) (σ (σ (M.op X0 (τ (τ X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq45256 (σ (M.op X0 (τ (τ X1)))) X1 X2
       have i₂ := eq45426 X0 (τ X1)
       grind)
    | exact superpose eq45426 eq45256
    | exact resolve eq45256 eq45426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45256 eq45426
  have eq53610 : ∀ X0 X1 : G, (k X1 X1) = (k (k X1 X1) (σ (σ (M.op X0 (τ (τ X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq374 (k X1 X1) X0
       have i₂ := eq46093 X1 X0
       grind)
    | exact superpose eq46093 eq374
    | exact resolve eq374 eq46093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374 eq46093
  have eq60056 : ∀ X0 X1 X2 : G, (M.op X0 (σ (σ (M.op X2 (τ (τ X0)))))) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39312 X1 X1 X0
       have i₂ := eq700 X0 X1
       grind)
    | exact superpose eq700 eq39312
    | (have j1 := eq700 X1 X0
       grind)
    | exact resolve eq39312 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700 eq39312
  have eq60477 : ∀ X0 X1 : G, (M.op X0 (σ (σ (τ (τ X0))))) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq60056 X0 X1 x
       have i₂ := eq44747 x (τ (τ X0)) X0
       grind)
    | exact superpose eq44747 eq60056
    | (have j0 := eq60056 X0 X1 x
       grind)
    | exact resolve eq60056 eq44747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44747 eq60056
  have eq60666 : ∀ X0 X1 : G, (M.op X0 (σ (τ X0))) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq60477 X0 X1
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq60477
    | (have j0 := eq60477 X0 X1
       grind)
    | exact resolve eq60477 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60477
  have eq60788 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq60666 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60666
    | (have j0 := eq60666 X0 X1
       grind)
    | exact resolve eq60666 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60666
  have eq96236 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1777 X0 X0
       have i₂ := eq60788 X0 X1
       grind)
    | exact superpose eq60788 eq1777
    | (have j0 := eq1777 X0 X0
       have j1 := eq60788 X0 X1
       grind)
    | (have r₁ := eq1777 X0 X0
       have r₂ := eq60788 X0 X1
       grind)
    | exact resolve eq1777 eq60788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1777 eq60788
  have eq96435 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq96236 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96236
  have eq96436 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq96435 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96435
  have eq98552 : ∀ X0 X1 X2 X3 : G, (σ (M.op X1 (τ X0))) = (M.op (σ (M.op X1 (τ X0))) X2) ∨ (M.op X3 X2) = (M.op X3 X0) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq40195 X0 X2 X0
       have i₂ := eq677 X0 X1 X2
       grind)
    | exact superpose eq677 eq40195
    | (have j1 := eq677 X2 X3 X0
       grind)
    | exact resolve eq40195 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq99418 : ∀ X0 X2 X3 : G, (M.op X0 X2) = (k X0 X2) ∨ (M.op X3 X2) = (M.op X3 X0) := by
    intro X0 X2 X3
    first
    | (have j0 := eq98552 X0 x X2 X3
       have j1 := eq51679 X0 X2 X0 X3
       grind)
    | (have r₁ := eq98552 x X0 X2 X3
       have r₂ := eq51679 X0 x X2 X3
       grind)
    | exact resolve eq98552 eq51679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51679 eq98552
  have eq99808 : ∀ X0 X1 X2 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X2 X0) = (M.op X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq99418 X0 (σ X1) X2
       grind)
    | exact superpose eq99418 eq22
    | (have j1 := eq99418 (σ X1) X0 X2
       grind)
    | exact resolve eq22 eq99418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99822 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X2 X0) = (M.op X2 (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq99418 X0 (τ X1) X2
       grind)
    | exact superpose eq99418 eq18
    | (have j1 := eq99418 (τ X1) X0 X2
       grind)
    | exact resolve eq18 eq99418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99915 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (σ X0)) = (M.op X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq99418 (σ X0) (σ X1) X2
       grind)
    | exact superpose eq99418 eq15
    | (have j1 := eq99418 (σ X1) (σ X0) X2
       grind)
    | exact resolve eq15 eq99418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99418
  have eq122058 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq96436 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96436
  have eq122060 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq122058 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122058
  have eq122133 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq122060 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq122060
    | exact resolve eq122060 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122134 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq122060 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq122060
    | exact resolve eq122060 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122340 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (σ X0)
       have i₂ := eq122060 (σ X0)
       grind)
    | exact superpose eq122060 eq28
    | (have j1 := eq122060 (σ X0)
       grind)
    | exact resolve eq28 eq122060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122349 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq122060 (τ X0)
       grind)
    | exact superpose eq122060 eq17
    | (have j1 := eq122060 (τ X0)
       grind)
    | exact resolve eq17 eq122060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122060
  have eq122360 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq122349 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq122349
    | (have j0 := eq122349 X0
       grind)
    | exact resolve eq122349 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122349
  have eq122368 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq122340 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq122340
    | (have j0 := eq122340 X0
       grind)
    | exact resolve eq122340 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122340
  have eq122426 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq122360 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq122360
    | (have j0 := eq122360 X0
       grind)
    | exact resolve eq122360 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122360
  have eq122433 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq122368 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq122368
    | (have j0 := eq122368 X0
       grind)
    | exact resolve eq122368 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122368
  have eq132637 : ∀ X0 : G, (τ (σ X0)) = (k X0 X0) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq122133 X0
       grind)
    | exact superpose eq122133 eq10
    | (have j1 := eq122133 X0
       grind)
    | exact resolve eq10 eq122133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122133
  have eq132774 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq132637 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq132637
    | (have j0 := eq132637 X0
       grind)
    | exact resolve eq132637 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132637
  have eq132808 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (σ (τ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq132774 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq132774
    | exact resolve eq132774 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132815 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2095 X0
       have i₂ := eq132774 X0
       grind)
    | exact superpose eq132774 eq2095
    | (have j0 := eq2095 X0
       have j1 := eq132774 X0
       grind)
    | exact resolve eq2095 eq132774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2095 eq132774
  have eq132937 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq132815 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132815
  have eq132981 : ∀ X0 : G, (k X0 X0) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq132808 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq132808
    | (have j0 := eq132808 X0
       grind)
    | exact resolve eq132808 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132808
  have eq133007 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq132981 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq132981
    | (have j0 := eq132981 X0
       grind)
    | exact resolve eq132981 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132981
  have eq133071 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k (k X0 X0) (σ X1)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 (k X0 X0) X1
       have i₂ := eq133007 X0
       grind)
    | exact superpose eq133007 eq17
    | (have j1 := eq133007 X0
       grind)
    | exact resolve eq17 eq133007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133007
  have eq133151 : ∀ X0 X1 : G, (k X0 (σ X1)) = (k (k X0 X0) (σ X1)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq133071 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq133071
    | (have j0 := eq133071 X0 X1
       grind)
    | exact resolve eq133071 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133071
  have eq136507 : ∀ X0 : G, (σ (τ X0)) = (k X0 X0) ∨ (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq122134 X0
       grind)
    | exact superpose eq122134 eq11
    | (have j1 := eq122134 X0
       grind)
    | exact resolve eq11 eq122134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122134
  have eq136592 : ∀ X0 : G, (k X0 X0) = X0 ∨ (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq136507 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq136507
    | (have j0 := eq136507 X0
       grind)
    | exact resolve eq136507 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136507
  have eq136768 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (k (k X0 (τ (σ X0))) (τ X1)) ∨ (τ (k (σ X0) (σ X0))) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 (σ X0) X1
       have i₂ := eq136592 (σ X0)
       grind)
    | exact superpose eq136592 eq41
    | (have j1 := eq136592 (σ X0)
       grind)
    | exact resolve eq41 eq136592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq136592
  have eq136799 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (k (k X0 X0) (τ X1)) ∨ (τ (k (σ X0) (σ X0))) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq136768 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq136768
    | (have j0 := eq136768 X0 X1
       grind)
    | exact resolve eq136768 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136768
  have eq136839 : ∀ X0 X1 : G, (k X0 (τ X1)) = (k (k X0 X0) (τ X1)) ∨ (τ (k (σ X0) (σ X0))) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq136799 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq136799
    | (have j0 := eq136799 X0 X1
       grind)
    | exact resolve eq136799 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq136799
  have eq136861 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (k X0 (τ X1)) = (k (k X0 X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq136839 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq136839
    | (have j0 := eq136839 X0 X1
       grind)
    | exact resolve eq136839 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136839
  have eq136879 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (k X0 (τ X1)) = (k (k X0 X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq136861 X0 X1
       have i₂ := eq22 (σ X0) X0
       grind)
    | exact superpose eq22 eq136861
    | (have j0 := eq136861 X0 X1
       grind)
    | exact resolve eq136861 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136861
  have eq136892 : ∀ X0 X1 : G, (k X0 (τ X1)) = (k (k X0 X0) (τ X1)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq136879 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq136879
    | (have j0 := eq136879 X0 X1
       grind)
    | exact resolve eq136879 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136879
  have eq140328 : ∀ X0 : G, (σ (τ X0)) = (k X0 X0) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq122426 X0
       grind)
    | exact superpose eq122426 eq11
    | (have j1 := eq122426 X0
       grind)
    | exact resolve eq11 eq122426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122426
  have eq140419 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq140328 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq140328
    | (have j0 := eq140328 X0
       grind)
    | exact resolve eq140328 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140328
  have eq140885 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq335 X0 (τ X0)
       have i₂ := eq140419 X0
       grind)
    | exact superpose eq140419 eq335
    | (have j1 := eq140419 X0
       grind)
    | exact resolve eq335 eq140419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335 eq140419
  have eq145568 : ∀ X0 : G, (τ (σ X0)) = (k X0 X0) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq122433 X0
       grind)
    | exact superpose eq122433 eq10
    | (have j1 := eq122433 X0
       grind)
    | exact resolve eq10 eq122433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122433
  have eq145711 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq145568 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq145568
    | (have j0 := eq145568 X0
       grind)
    | exact resolve eq145568 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145568
  have eq145972 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq145711 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq145711
    | (have j0 := eq145711 (τ X0)
       grind)
    | exact resolve eq145711 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145711
  have eq146440 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq145972 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq145972
    | (have j0 := eq145972 X0
       grind)
    | exact resolve eq145972 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145972
  have eq146550 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq146440 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq146440
    | (have j0 := eq146440 X0
       grind)
    | exact resolve eq146440 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146440
  have eq187528 : ∀ X0 X1 X2 : G, (k X1 (k (τ X0) X1)) = X1 ∨ (M.op X2 X0) = (M.op X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq416 X1 X0
       have i₂ := eq99808 X0 X1 X2
       grind)
    | exact superpose eq99808 eq416
    | (have j1 := eq99808 X0 X1 X2
       grind)
    | exact resolve eq416 eq99808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416 eq99808
  have eq188154 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (k (τ X1) (τ X0)))) ∨ (M.op X2 X1) = (M.op X2 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (k (τ X1) (τ X0))
       have i₂ := eq187528 X1 (τ X0) X2
       grind)
    | exact superpose eq187528 eq17
    | (have j1 := eq187528 X1 (τ X0) X2
       grind)
    | exact resolve eq17 eq187528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187528
  have eq188163 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (k (σ (τ X1)) X0)) ∨ (M.op X2 X1) = (M.op X2 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq188154 X0 X1 X2
       have i₂ := eq18 X0 (τ X1)
       grind)
    | exact superpose eq18 eq188154
    | (have j0 := eq188154 X0 X1 X2
       grind)
    | exact resolve eq188154 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188154
  have eq188246 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (k X1 X0)) ∨ (M.op X2 X1) = (M.op X2 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq188163 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq188163
    | (have j0 := eq188163 X0 X1 X2
       grind)
    | exact resolve eq188163 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188163
  have eq188289 : ∀ X0 X1 X2 : G, (k X0 (k X1 X0)) = X0 ∨ (M.op X2 X1) = (M.op X2 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq188246 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq188246
    | (have j0 := eq188246 X0 X1 X2
       grind)
    | exact resolve eq188246 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188246
  have eq188320 : ∀ X0 X1 X2 : G, (k X0 (k X1 X0)) = X0 ∨ (M.op X2 X1) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq188289 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq188289
    | (have j0 := eq188289 X0 X1 X2
       grind)
    | exact resolve eq188289 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188289
  have eq188561 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (k X1 (τ X0)))) ∨ (M.op X2 X1) = (M.op X2 (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (k X1 (τ X0))
       have i₂ := eq188320 (τ X0) X1 X2
       grind)
    | exact superpose eq188320 eq17
    | (have j1 := eq188320 (τ X0) X1 X2
       grind)
    | exact resolve eq17 eq188320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq188320
  have eq188572 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (k (σ X1) X0)) ∨ (M.op X2 X1) = (M.op X2 (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq188561 X0 X1 X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq188561
    | (have j0 := eq188561 X0 X1 X2
       grind)
    | exact resolve eq188561 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188561
  have eq188641 : ∀ X0 X1 X2 : G, (k X0 (k (σ X1) X0)) = X0 ∨ (M.op X2 X1) = (M.op X2 (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq188572 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq188572
    | (have j0 := eq188572 X0 X1 X2
       grind)
    | exact resolve eq188572 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188572
  have eq190147 : ∀ X0 X1 X2 : G, (k X1 (k X0 X1)) = X1 ∨ (M.op X2 (τ X0)) = (M.op X2 (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq188641 X1 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq188641
    | (have j0 := eq188641 X1 (τ X0) X2
       grind)
    | exact resolve eq188641 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188641
  have eq191511 : ∀ X0 X1 X2 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X2 X1) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq99822 X0 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq99822
    | exact resolve eq99822 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99822
  have eq191986 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X2 X1) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq191511 X0 X1 X2
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq191511
    | (have j0 := eq191511 X0 X1 X2
       grind)
    | exact resolve eq191511 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191511
  have eq192351 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (k X0 X1)) = (M.op X2 (τ (M.op X3 (σ (M.op X0 X1))))) ∨ (M.op X4 X1) = (M.op X4 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq43355 X3 (k X0 X1) X2
       have i₂ := eq191986 X1 X0 X4
       grind)
    | exact superpose eq191986 eq43355
    | (have j1 := eq191986 (τ (M.op X3 (σ (M.op X0 X1)))) (k X0 X1) X2
       grind)
    | exact resolve eq43355 eq191986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192467 : ∀ X0 X1 X2 X4 : G, (M.op X2 X1) = (M.op X2 (k X0 X1)) ∨ (M.op X4 X1) = (M.op X4 X0) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq192351 X0 X1 X2 x X4
       have i₂ := eq40572 X0 X1 X2 x
       grind)
    | exact superpose eq40572 eq192351
    | (have j0 := eq192351 (k X0 X1) X1 X2 x X2
       grind)
    | exact resolve eq192351 eq40572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40572 eq192351
  have eq192768 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op X1 (k X2 X0)) ∨ (M.op X3 X0) = (M.op X3 (k X2 X0)) ∨ (M.op X4 (τ X0)) = (M.op X4 (τ X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq192467 X0 (k X2 X0) X1 X3
       have i₂ := eq190147 X2 X0 X4
       grind)
    | exact superpose eq190147 eq192467
    | (have j0 := eq192467 X2 X0 X1 X4
       have j1 := eq190147 X0 X2 X4
       grind)
    | exact resolve eq192467 eq190147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190147
  have eq193397 : ∀ X0 X1 X2 X4 : G, (M.op X1 X0) = (M.op X1 (k X2 X0)) ∨ (M.op X4 (τ X0)) = (M.op X4 (τ X2)) := by
    intro X0 X1 X2 X4
    first
    | (have j0 := eq192768 X0 X1 X2 X1 X4
       have j1 := eq39481 X1 X1 X0 (k X2 X0)
       grind)
    | (have r₁ := eq192768 X2 X1 X2 x X4
       have r₂ := eq39481 X0 X1 X2 (k X2 X2)
       grind)
    | (have r₁ := eq192768 x X1 X2 x X4
       have r₂ := eq39481 X0 X1 (k X2 x) x
       grind)
    | (have r₁ := eq192768 X2 X1 X2 X1 X4
       have r₂ := eq39481 X0 X1 X2 (k X2 X2)
       grind)
    | exact resolve eq192768 eq39481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192768
  have eq230871 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) (σ (σ (τ (τ X0))))) ∨ (σ (k (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq51727 (τ (τ X0)) X0 X1
       have i₂ := eq132937 (τ X0)
       grind)
    | exact superpose eq132937 eq51727
    | (have j1 := eq132937 (τ X0)
       grind)
    | exact resolve eq51727 eq132937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51727
  have eq230874 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (σ (σ (τ (τ X0))))) ∨ (σ (k (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq53610 (τ (τ X0)) X0
       have i₂ := eq132937 (τ X0)
       grind)
    | exact superpose eq132937 eq53610
    | (have j1 := eq132937 (τ X0)
       grind)
    | exact resolve eq53610 eq132937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53610 eq132937
  have eq231194 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (σ (τ X0))) ∨ (σ (k (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq230874 X0
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq230874
    | (have j0 := eq230874 X0
       grind)
    | exact resolve eq230874 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230874
  have eq231197 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) (σ (τ X0))) ∨ (σ (k (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq230871 X0 X1
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq230871
    | (have j0 := eq230871 X0 X1
       grind)
    | exact resolve eq230871 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230871
  have eq231296 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ (k (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq231194 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq231194
    | (have j0 := eq231194 X0
       grind)
    | exact resolve eq231194 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231194
  have eq231299 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) ∨ (σ (k (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq231197 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq231197
    | (have j0 := eq231197 X0 X1
       grind)
    | exact resolve eq231197 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231197
  have eq231336 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq231296 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq231296
    | (have j0 := eq231296 X0
       grind)
    | exact resolve eq231296 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231296
  have eq231338 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X1 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq231299 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq231299
    | (have j0 := eq231299 X0 X1
       grind)
    | exact resolve eq231299 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231299
  have eq231358 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq231336 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq231336
    | (have j0 := eq231336 X0
       grind)
    | exact resolve eq231336 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231336
  have eq231360 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X1 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq231338 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq231338
    | (have j0 := eq231338 X0 X1
       grind)
    | exact resolve eq231338 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq231338
  have eq231377 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq231358 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq231358
    | (have j0 := eq231358 X0
       grind)
    | exact resolve eq231358 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231358
  have eq231379 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq231360 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq231360
    | (have j0 := eq231360 X0 X1
       grind)
    | exact resolve eq231360 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231360
  have eq232065 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = (k X0 (k X0 X0)) ∨ (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq989 (k X0 X0) X0
       have i₂ := eq231377 X0
       grind)
    | exact superpose eq231377 eq989
    | (have j0 := eq989 (k X0 X0) X0
       have j1 := eq231377 X0
       grind)
    | exact resolve eq989 eq231377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232119 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = (k X0 (k X0 X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq232065 X0
       have j1 := eq44291 X0 X0
       grind)
    | (have r₁ := eq232065 x
       have r₂ := eq44291 (k x x) x
       grind)
    | (have r₁ := eq232065 x
       have r₂ := eq44291 x x
       grind)
    | exact resolve eq232065 eq44291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44291 eq232065
  have eq232159 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq232119 X0
       have j1 := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq232119 X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | exact resolve eq232119 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232119
  have eq232393 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq232159 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232159
  have eq232472 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq232393 X0
       have j1 := eq140885 X0
       grind)
    | (have r₁ := eq232393 X0
       have r₂ := eq140885 X0
       grind)
    | exact resolve eq232393 eq140885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140885 eq232393
  have eq232631 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (k (k X0 X0) X0) = X0 ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq989 X0 (k X0 X0)
       have i₂ := eq232472 X0
       grind)
    | exact superpose eq232472 eq989
    | (have j0 := eq989 X0 (k X0 X0)
       grind)
    | exact resolve eq989 eq232472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989 eq232472
  have eq232691 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq232631 X0
       have j1 := eq12 (k X0 X0) X0
       grind)
    | (have r₁ := eq232631 x
       have r₂ := eq12 (k x x) x
       grind)
    | exact resolve eq232631 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232631
  have eq232918 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq232691 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232691
  have eq233205 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (k (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq232918 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq232918
    | exact resolve eq232918 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232918
  have eq233280 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (τ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq233205 X0
       have i₂ := eq31 X0 (k X0 X0)
       grind)
    | exact superpose eq31 eq233205
    | (have j0 := eq233205 X0
       grind)
    | exact resolve eq233205 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233205
  have eq233400 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (τ (k (k X0 X0) X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq233280 X0
       have i₂ := eq146550 X0
       grind)
    | exact superpose eq146550 eq233280
    | (have j0 := eq233280 X0
       have j1 := eq146550 X0
       grind)
    | (have r₁ := eq233280 X0
       have r₂ := eq146550 X0
       grind)
    | exact resolve eq233280 eq146550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146550
  have eq233521 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (τ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq233400 X0
       have j1 := eq233280 X0
       grind)
    | (have r₁ := eq233400 X0
       have r₂ := eq233280 X0
       grind)
    | exact resolve eq233400 eq233280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233280 eq233400
  have eq365625 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ X0)) ∨ (τ (σ X0)) = (τ (k (k (σ X0) (σ X0)) (σ X0))) ∨ (k (k X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq233521 (σ X0)
       have i₂ := eq3418 X0 X1
       grind)
    | exact superpose eq3418 eq233521
    | (have j0 := eq233521 (σ X0)
       have j1 := eq3418 X0 X1
       grind)
    | exact resolve eq233521 eq3418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3418 eq233521
  have eq365829 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (k (k (σ X0) (σ X0)) (σ X0))) ∨ (k (k X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq365625 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365625
  have eq365920 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (k (k X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq365829 X0 X1
       have i₂ := eq22 (k (σ X0) (σ X0)) X0
       grind)
    | exact superpose eq22 eq365829
    | (have j0 := eq365829 X0 X1
       grind)
    | exact resolve eq365829 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365829
  have eq366083 : ∀ X0 X1 : G, (τ (σ X0)) = (k (k (τ (σ X0)) X0) X0) ∨ (k (k X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq365920 X0 X1
       have i₂ := eq22 (σ X0) X0
       grind)
    | exact superpose eq22 eq365920
    | (have j0 := eq365920 X0 X1
       grind)
    | exact resolve eq365920 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq365920
  have eq366140 : ∀ X0 X1 : G, (k (k X0 X0) X0) = X0 ∨ (k (k X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq366083 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq366083
    | (have j0 := eq366083 X0 X1
       grind)
    | exact resolve eq366083 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366083
  have eq366416 : ∀ X0 : G, (k (M.op X0 X0) X0) ≠ X0 ∨ (k (k X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq366140 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366140
  have eq366717 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq366416 X0
       have i₂ := eq231379 X0 X0
       grind)
    | exact superpose eq231379 eq366416
    | (have j1 := eq231379 X0 x
       grind)
    | exact resolve eq366416 eq231379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231379 eq366416
  have eq366781 : ∀ X0 : G, (M.op X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq366717 X0
       have j1 := eq697 X0
       grind)
    | (have r₁ := eq366717 X0
       have r₂ := eq697 X0
       grind)
    | exact resolve eq366717 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697 eq366717
  have eq367630 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq231377 X0
       have i₂ := eq366781 X0
       grind)
    | exact superpose eq366781 eq231377
    | (have j0 := eq231377 X0
       have j1 := eq366781 X0
       grind)
    | exact resolve eq231377 eq366781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231377
  have eq367662 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq133151 (σ X0) X0
       have i₂ := eq366781 (σ X0)
       grind)
    | exact superpose eq366781 eq133151
    | (have j0 := eq133151 (σ X0) x
       have j1 := eq366781 (σ X0)
       grind)
    | exact resolve eq133151 eq366781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133151
  have eq367666 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq136892 (τ X0) X0
       have i₂ := eq366781 (τ X0)
       grind)
    | exact superpose eq366781 eq136892
    | (have j0 := eq136892 (τ X0) x
       have j1 := eq366781 (τ X0)
       grind)
    | exact resolve eq136892 eq366781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136892 eq366781
  have eq367744 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq367666 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367666
  have eq367745 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq367662 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367662
  have eq367753 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq367630 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367630
  have eq367798 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq367744 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq367744
    | exact resolve eq367744 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq367744
  have eq367801 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq367745 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq367745
    | exact resolve eq367745 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367745
  have eq367811 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq367798 X0
       have i₂ := eq367753 X0
       grind)
    | exact superpose eq367753 eq367798
    | exact resolve eq367798 eq367753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367798
  have eq367812 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq367801 X0
       have i₂ := eq367753 X0
       grind)
    | exact superpose eq367753 eq367801
    | exact resolve eq367801 eq367753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367753 eq367801
  have eq368719 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) X1))) = X0 ∨ (M.op (τ X0) X1) ≠ (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq102 X0 (τ X0) X1
       have i₂ := eq367811 X0
       grind)
    | exact superpose eq367811 eq102
    | (have j0 := eq102 X0 (τ X0) X1
       grind)
    | exact resolve eq102 eq367811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq367811
  have eq371870 : ∀ X0 X1 : G, (k X0 (τ (M.op (σ X0) X1))) = X0 ∨ (M.op (σ X0) X1) ≠ (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq103 X0 (σ X0) X1
       have i₂ := eq367812 X0
       grind)
    | exact superpose eq367812 eq103
    | (have j0 := eq103 X0 (σ X0) X1
       grind)
    | exact resolve eq103 eq367812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq435907 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X1 (σ (M.op (τ X0) X2))) ∨ (M.op X3 X0) = (M.op X3 (σ (M.op (τ X0) X2))) ∨ (τ (M.op X0 X0)) ≠ (M.op (τ X0) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq192467 X0 (σ (M.op (τ X0) X2)) X1 X3
       have i₂ := eq368719 X0 X2
       grind)
    | exact superpose eq368719 eq192467
    | (have j0 := eq192467 (σ (M.op (τ X0) X2)) X0 X2 X1
       have j1 := eq368719 X0 X2
       grind)
    | exact resolve eq192467 eq368719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192467 eq368719
  have eq436017 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (σ (M.op (τ X0) X2))) ∨ (τ (M.op X0 X0)) ≠ (M.op (τ X0) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq435907 X0 X1 X2 X1
       have j1 := eq39481 X1 X1 X0 (σ (M.op (τ X0) X2))
       grind)
    | (have r₁ := eq435907 X2 X1 X2 x
       have r₂ := eq39481 X0 X1 X2 (σ (M.op (τ X2) X2))
       grind)
    | (have r₁ := eq435907 x X1 X2 x
       have r₂ := eq39481 X0 X1 (σ (M.op (τ x) X2)) x
       grind)
    | (have r₁ := eq435907 X2 X1 X2 X1
       have r₂ := eq39481 X0 X1 X2 (σ (M.op (τ X2) X2))
       grind)
    | exact resolve eq435907 eq39481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39481 eq435907
  have eq436270 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) ≠ (M.op (τ X0) X2) ∨ (M.op X1 X0) = (M.op X1 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq436017 X0 X1 X2
       have i₂ := eq43357 X1 X2 (τ X0)
       grind)
    | exact superpose eq43357 eq436017
    | (have j0 := eq436017 X0 X1 X2
       grind)
    | exact resolve eq436017 eq43357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436017
  have eq436921 : ∀ X0 X1 X2 X3 X4 : G, (M.op (τ (σ (M.op X0 (τ (M.op X1 X2))))) X3) ≠ (τ (M.op (σ (M.op X0 (τ (M.op X1 X2)))) X2)) ∨ (M.op X4 (σ (M.op X0 (τ (M.op X1 X2))))) = (M.op X4 (σ X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq436270 (σ (M.op X0 (τ (M.op X1 X2)))) X4 X3
       have i₂ := eq39730 X1 X2 (σ (M.op X0 (τ (M.op X1 X2)))) X0
       grind)
    | exact superpose eq39730 eq436270
    | (have j0 := eq436270 (σ (M.op X0 (τ (M.op X1 X2)))) X4 X3
       grind)
    | exact resolve eq436270 eq39730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436270
  have eq437624 : ∀ X0 X1 X2 X3 X4 : G, (τ (σ (M.op X0 (τ (M.op X1 X2))))) ≠ (M.op (τ (σ (M.op X0 (τ (M.op X1 X2))))) X3) ∨ (M.op X4 (σ (M.op X0 (τ (M.op X1 X2))))) = (M.op X4 (σ X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq436921 X0 X1 X2 X3 X4
       have i₂ := eq40195 X0 X1 X2
       grind)
    | exact superpose eq40195 eq436921
    | (have j0 := eq436921 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq436921 eq40195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40195 eq436921
  have eq437888 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (τ (M.op X1 X2))) ≠ (M.op (M.op X0 (τ (M.op X1 X2))) X3) ∨ (M.op X4 (σ (M.op X0 (τ (M.op X1 X2))))) = (M.op X4 (σ X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq437624 X0 X1 X2 X3 X4
       have i₂ := eq10 (M.op X0 (τ (M.op X1 X2)))
       grind)
    | exact superpose eq10 eq437624
    | (have j0 := eq437624 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq437624 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437624
  have eq438065 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) ≠ (M.op X0 (τ (M.op X1 X2))) ∨ (M.op X4 (σ (M.op X0 (τ (M.op X1 X2))))) = (M.op X4 (σ X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq437888 X0 X1 X2 X3 X4
       have i₂ := eq65 X0 (τ (M.op X1 X2)) X3
       grind)
    | exact superpose eq65 eq437888
    | (have j0 := eq437888 X0 X1 X2 X3 X4
       grind)
    | (have r₁ := eq437888 X0 X1 X2 (τ (M.op X1 X2)) X4
       have r₂ := eq65 X0 (τ (M.op X1 X2)) (τ (M.op X1 X2))
       grind)
    | exact resolve eq437888 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437888
  have eq438188 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) ≠ (M.op X0 (τ X2)) ∨ (M.op X4 (σ (M.op X0 (τ (M.op X1 X2))))) = (M.op X4 (σ X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq438065 X0 X1 X2 X3 X4
       have i₂ := eq43608 X2 X0 X1
       grind)
    | exact superpose eq43608 eq438065
    | (have j0 := eq438065 X0 X1 X2 X3 X4
       grind)
    | (have r₁ := eq438065 X1 X2 X0 (τ X0) X4
       have r₂ := eq43608 X0 X1 X2
       grind)
    | (have r₁ := eq438065 X1 X1 X2 (τ (M.op X2 (M.op X1 X2))) X4
       have r₂ := eq43608 (M.op X1 X2) X1 X2
       grind)
    | exact resolve eq438065 eq43608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438065
  have eq438252 : ∀ X0 X2 X3 X4 : G, (M.op X0 X3) ≠ (M.op X0 (τ X2)) ∨ (M.op X4 X2) = (M.op X4 (σ X3)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq438188 X0 x X2 X3 X4
       have i₂ := eq39730 x X2 X4 X0
       grind)
    | exact superpose eq39730 eq438188
    | (have j0 := eq438188 X0 x X2 X3 X4
       grind)
    | (have r₁ := eq438188 X2 x X2 (σ (M.op X3 (τ (M.op X0 (τ X2))))) X4
       have r₂ := eq39730 X0 (τ X2) X2 X3
       grind)
    | exact resolve eq438188 eq39730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39730 eq438188
  have eq440629 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (τ X3)) ≠ (M.op X0 (τ (τ X1))) ∨ (M.op X4 X3) = (M.op X4 (σ (τ (τ (τ (M.op X2 (σ X1))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq438252 X0 X3 (τ (τ (τ (M.op X2 (σ X1))))) X4
       have i₂ := eq50004 X1 X0 X2
       grind)
    | exact superpose eq50004 eq438252
    | (have j0 := eq438252 X0 (τ X1) (τ X3) X4
       grind)
    | (have r₁ := eq438252 X2 (τ (τ (M.op X3 (σ X1)))) (τ (τ X1)) X4
       have r₂ := eq50004 X1 X2 X3
       grind)
    | (have r₁ := eq438252 X2 (τ X1) (τ (τ (τ (M.op X3 (σ X1))))) X4
       have r₂ := eq50004 X1 X2 X3
       grind)
    | exact resolve eq438252 eq50004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50004 eq438252
  have eq441132 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X3) = (M.op X4 (τ (τ (M.op X2 (σ X1))))) ∨ (M.op X0 (τ X3)) ≠ (M.op X0 (τ (τ X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq440629 X0 X1 X2 X3 X4
       have i₂ := eq11 (τ (τ (M.op X2 (σ X1))))
       grind)
    | exact superpose eq11 eq440629
    | (have j0 := eq440629 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq440629 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440629
  have eq441364 : ∀ X0 X1 X3 X4 : G, (M.op X0 (τ X3)) ≠ (M.op X0 (τ (τ X1))) ∨ (M.op X4 X3) = (M.op X4 (τ X1)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq441132 X0 X1 x X3 X4
       have i₂ := eq44071 X1 X4 x
       grind)
    | exact superpose eq44071 eq441132
    | (have j0 := eq441132 X0 X1 x X3 X4
       grind)
    | (have r₁ := eq441132 x (M.op X4 (σ X1)) x X1 X4
       have r₂ := eq44071 X1 x X4
       grind)
    | (have r₁ := eq441132 x X1 x (τ (M.op X4 (σ (τ X1)))) X4
       have r₂ := eq44071 (τ X1) x X4
       grind)
    | exact resolve eq441132 eq44071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44071 eq441132
  have eq447423 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X1 (τ (M.op (σ X0) X2))) ∨ (M.op X3 (τ X0)) = (M.op X3 (τ (τ (M.op (σ X0) X2)))) ∨ (σ (M.op X0 X0)) ≠ (M.op (σ X0) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq193397 (τ (M.op (σ X0) X2)) X1 X0 X3
       have i₂ := eq371870 X0 X2
       grind)
    | exact superpose eq371870 eq193397
    | (have j0 := eq193397 X0 X1 (τ (M.op (σ X0) X2)) X3
       have j1 := eq371870 X0 X2
       grind)
    | exact resolve eq193397 eq371870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193397 eq371870
  have eq447517 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (τ (M.op (σ X0) X2))) ∨ (σ (M.op X0 X0)) ≠ (M.op (σ X0) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq447423 X0 X1 X2 x
       have j1 := eq441364 X0 (M.op (σ X0) X2) X0 X1
       grind)
    | (have r₁ := eq447423 (τ (τ X1)) X0 X2 x
       have r₂ := eq441364 X0 X1 (M.op (σ (τ (τ X1))) X2) x
       grind)
    | (have r₁ := eq447423 x X1 X2 X0
       have r₂ := eq441364 X0 (M.op (σ x) X2) x x
       grind)
    | (have r₁ := eq447423 (τ X1) X1 X2 X0
       have r₂ := eq441364 X0 X1 (τ (M.op (σ (τ X1)) X2)) x
       grind)
    | exact resolve eq447423 eq441364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441364 eq447423
  have eq447763 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X2) ∨ (M.op X1 X0) = (M.op X1 (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq447517 X0 X1 X2
       have i₂ := eq43608 X2 X1 (σ X0)
       grind)
    | exact superpose eq43608 eq447517
    | (have j0 := eq447517 X0 X1 X2
       grind)
    | exact resolve eq447517 eq43608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43608 eq447517
  have eq448462 : ∀ X0 X1 X2 X3 : G, (M.op (σ (τ (M.op X0 (σ X1)))) X2) ≠ (σ (M.op (τ (M.op X0 (σ X1))) X1)) ∨ (M.op X3 (τ X2)) = (M.op X3 (τ (M.op X0 (σ X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq447763 (τ (M.op X0 (σ X1))) X3 X2
       have i₂ := eq43355 X0 X1 (τ (M.op X0 (σ X1)))
       grind)
    | exact superpose eq43355 eq447763
    | (have j0 := eq447763 (τ X2) X3 (M.op X0 (σ X1))
       grind)
    | exact resolve eq447763 eq43355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447763
  have eq449098 : ∀ X0 X1 X2 X3 : G, (σ (τ (M.op X0 (σ X1)))) ≠ (M.op (σ (τ (M.op X0 (σ X1)))) X2) ∨ (M.op X3 (τ X2)) = (M.op X3 (τ (M.op X0 (σ X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq448462 X0 X1 X2 X3
       have i₂ := eq43971 X0 X1
       grind)
    | exact superpose eq43971 eq448462
    | (have j0 := eq448462 X0 X1 X2 X3
       grind)
    | exact resolve eq448462 eq43971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43971 eq448462
  have eq449375 : ∀ X0 X1 X2 X3 : G, (M.op X0 (σ X1)) ≠ (M.op (M.op X0 (σ X1)) X2) ∨ (M.op X3 (τ X2)) = (M.op X3 (τ (M.op X0 (σ X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq449098 X0 X1 X2 X3
       have i₂ := eq11 (M.op X0 (σ X1))
       grind)
    | exact superpose eq11 eq449098
    | (have j0 := eq449098 X0 X1 X2 X3
       grind)
    | exact resolve eq449098 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449098
  have eq449560 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) ≠ (M.op X0 (σ X1)) ∨ (M.op X3 (τ X2)) = (M.op X3 (τ (M.op X0 (σ X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq449375 X0 X1 X2 X3
       have i₂ := eq65 X0 (σ X1) X2
       grind)
    | exact superpose eq65 eq449375
    | (have j0 := eq449375 X0 X1 X2 X3
       grind)
    | (have r₁ := eq449375 X0 X1 (σ X1) X3
       have r₂ := eq65 X0 (σ X1) (σ X1)
       grind)
    | exact resolve eq449375 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq449375
  have eq449690 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) ≠ (M.op X0 (σ X1)) ∨ (M.op X3 X1) = (M.op X3 (τ X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq449560 X0 X1 X2 X3
       have i₂ := eq43355 X0 X1 X3
       grind)
    | exact superpose eq43355 eq449560
    | (have j0 := eq449560 X0 X1 X2 X3
       grind)
    | (have r₁ := eq449560 X2 X1 (τ (M.op X0 (σ (σ X1)))) X3
       have r₂ := eq43355 X0 (σ X1) X2
       grind)
    | exact resolve eq449560 eq43355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43355 eq449560
  have eq452013 : ∀ X0 X1 X2 X3 : G, (M.op X0 (σ X1)) ≠ (M.op X0 (σ X2)) ∨ (M.op X3 X2) = (M.op X3 (τ (σ (k X1 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq449690 X0 X2 (σ (k X1 X1)) X3
       have i₂ := eq44106 X1 X0
       grind)
    | exact superpose eq44106 eq449690
    | (have j0 := eq449690 X0 X2 (σ X1) X3
       grind)
    | (have r₁ := eq449690 X1 (k X0 X0) (σ X0) X3
       have r₂ := eq44106 X0 X1
       grind)
    | (have r₁ := eq449690 X1 X0 (σ (k X0 X0)) X3
       have r₂ := eq44106 X0 X1
       grind)
    | exact resolve eq449690 eq44106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44106 eq449690
  have eq452719 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (M.op X3 (k X1 X1)) ∨ (M.op X0 (σ X1)) ≠ (M.op X0 (σ X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq452013 X0 X1 X2 X3
       have i₂ := eq10 (k X1 X1)
       grind)
    | exact superpose eq10 eq452013
    | (have j0 := eq452013 X0 X1 X2 X3
       grind)
    | exact resolve eq452013 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452013
  have eq452918 : ∀ X0 X1 X2 X3 : G, (M.op X0 (σ X1)) ≠ (M.op X0 (σ X2)) ∨ (M.op X3 X1) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq452719 X0 X2 X1 X3
       have i₂ := eq44090 X2 X3
       grind)
    | exact superpose eq44090 eq452719
    | (have j0 := eq452719 X0 X1 X2 X3
       grind)
    | exact resolve eq452719 eq44090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44090 eq452719
  have eq580801 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq99915 x y X0
       grind)
    | exact superpose eq99915 eq16
    | (have j1 := eq99915 y x X0
       grind)
    | exact resolve eq16 eq99915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99915
  have eq591912 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (M.op X1 x) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq580801 X0
       have i₂ := eq191986 y x X1
       grind)
    | exact superpose eq191986 eq580801
    | (have j0 := eq580801 X0
       have j1 := eq191986 (σ x) (σ y) X0
       grind)
    | (have r₁ := eq580801 X0
       have r₂ := eq191986 y x x
       grind)
    | exact resolve eq580801 eq191986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191986 eq580801
  have eq591913 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (M.op X1 x) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have j0 := eq591912 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591912
  have eq591922 : ∀ X1 : G, (M.op X1 x) = (M.op X1 y) := by
    intro X1
    first
    | (have j0 := eq591913 x X1
       have j1 := eq452918 x x y X1
       grind)
    | (have r₁ := eq591913 x X1
       have r₂ := eq452918 x y x x
       grind)
    | (have r₁ := eq591913 x X1
       have r₂ := eq452918 x x y x
       grind)
    | exact resolve eq591913 eq452918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452918 eq591913
  have eq592366 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X1 (σ (M.op X0 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq43357 X1 y X0
       have i₂ := eq591922 X0
       grind)
    | exact superpose eq591922 eq43357
    | exact resolve eq43357 eq591922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq592565 : ∀ X1 : G, (M.op X1 (σ y)) = (M.op X1 (σ x)) := by
    intro X1
    first
    | (have i₁ := eq592366 x X1
       have i₂ := eq43357 X1 x x
       grind)
    | exact superpose eq43357 eq592366
    | exact resolve eq592366 eq43357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43357 eq592366
  have eq595909 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq592565 (σ x)
       grind)
    | exact superpose eq592565 eq16
    | exact resolve eq16 eq592565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592565
  have eq595967 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq595909
       have i₂ := eq367812 x
       grind)
    | exact superpose eq367812 eq595909
    | exact resolve eq595909 eq367812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367812 eq595909
  have eq596478 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq595967
       have i₂ := eq591922 x
       grind)
    | exact superpose eq591922 eq595967
    | exact resolve eq595967 eq591922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591922 eq595967
  have eq596479 : False := by grind
  exact eq596479

/-- `Equation3744`: `x ◇ y = (x ◇ z) ◇ (w ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = X then Y else m(Y,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxy_y_pyy_Equation3744 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) Law3744 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3744.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq26 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq62 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X2 (M.op X3 X1) X4 (M.op X0 x)
       have i₂ := eq9 X0 X1 x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq62 x X1 X2 X3 x
       have i₂ := eq9 X2 X1 x x
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq89 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X2 (M.op X0 X1)) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 X1)
       have i₂ := eq9 X0 X1 X1 X0
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X2 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op x X1)
       have r₂ := eq9 x X1 X1 x
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq89 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq95 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq92 X0 X1 X2
       have i₂ := eq63 X1 X2 X0
       grind)
    | exact superpose eq63 eq92
    | exact resolve eq92 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq92
  have eq831 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq833 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq831 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq836 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq833 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq833 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq833 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833
  have eq871 : ∀ X0 X1 : G, (k (σ X1) (M.op (σ X0) (σ X0))) = (σ (k X1 (k X0 (τ (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 (σ X0) X1
       have i₂ := eq836 (σ X0)
       grind)
    | exact superpose eq836 eq26
    | exact resolve eq26 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq884 : ∀ X0 X1 : G, (k (σ X1) (M.op (σ X0) (σ X0))) = (σ (k X1 (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq871 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq871
    | exact resolve eq871 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq915 : ∀ X0 X1 : G, (k (σ X1) (M.op (σ X0) (σ X0))) = (σ (k X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq884 X0 X1
       have i₂ := eq836 X0
       grind)
    | exact superpose eq836 eq884
    | exact resolve eq884 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836 eq884
  have eq941 : ∀ X0 X1 : G, (k (σ X1) (M.op (σ X0) (σ X0))) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq915 X0 X1
       have i₂ := eq95 X0 X0 X1
       grind)
    | exact superpose eq95 eq915
    | exact resolve eq915 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915
  have eq963 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq941 X0 X1
       have i₂ := eq95 (σ X0) (σ X0) (σ X1)
       grind)
    | exact superpose eq95 eq941
    | exact resolve eq941 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq941
  have eq1051 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq963 y x
       grind)
    | exact superpose eq963 eq16
    | (have r₁ := eq16
       have r₂ := eq963 y x
       grind)
    | exact resolve eq16 eq963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq1072 : False := by grind
  exact eq1072

/-- `Equation3751`: `x ◇ y = (y ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_x_pxy_Equation3751 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3751 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3751.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq19 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq10
    | exact resolve eq10 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X1) X2
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 (M.op X0 X1) X2
       grind)
    | (have r₁ := eq12 (M.op X0 X1) X1
       have r₂ := eq19 X0 X1
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq70 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 X2 : G, (k (σ (M.op X0 X1)) X2) = (σ (M.op (M.op X0 X1) (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X2 (M.op X0 X1)
       have i₂ := eq71 X0 X1 (τ X2)
       grind)
    | exact superpose eq71 eq18
    | exact resolve eq18 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 X1 X2 : G, (k (σ (M.op X1 X2)) X0) = (σ (M.op (τ X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq89 X1 X2 X0
       have i₂ := eq67 (M.op X1 X2) (τ X0)
       grind)
    | (have i₁ := eq89 X1 X2 X0
       have i₂ := eq67 (τ X0) (M.op X1 X2)
       grind)
    | exact superpose eq67 eq89
    | exact resolve eq89 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (k (σ (M.op X1 X2)) (σ X0)) = (σ (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq130 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq130
    | exact resolve eq130 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq207 : ∀ X0 X1 X2 : G, (σ (k (M.op X1 X2) X0)) = (σ (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq182 X0 X1 X2
       have i₂ := eq15 (M.op X1 X2) X0
       grind)
    | exact superpose eq15 eq182
    | exact resolve eq182 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq217 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X1 X2) X0)) = (σ (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq207 X0 X1 X2
       have i₂ := eq71 X1 X2 X0
       grind)
    | exact superpose eq71 eq207
    | exact resolve eq207 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq229 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq75 X0 (k X1 (τ X0))
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq75
    | (have j0 := eq75 X2 X2
       grind)
    | exact resolve eq75 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ (k X0 X1)) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X1) (σ X0)
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq9
    | (have j1 := eq75 X1 X1
       grind)
    | exact resolve eq9 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X0) (σ X1)
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq19
    | (have j1 := eq75 (k X0 X1) (k X0 X1)
       grind)
    | exact resolve eq19 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq248 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (M.op X1 X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq75 X0 X0
       grind)
    | exact superpose eq75 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq75 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq75 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq75 X0 X1
       grind)
    | exact resolve eq13 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq75 X0 X0
       grind)
    | exact superpose eq75 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq75 X0 X0
       grind)
    | (have r₁ := eq12 (σ X1) X1
       have r₂ := eq75 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) X1
       have r₂ := eq75 X0 X1
       grind)
    | exact resolve eq12 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq75 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq252 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq251 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq254 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq249 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq255 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (M.op X1 X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq248 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq256 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq254 X0 X1
       have j1 := eq12 (σ X0) X1
       grind)
    | (have r₁ := eq254 X0 X1
       have r₂ := eq12 (σ X0) X1
       grind)
    | exact resolve eq254 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq257 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq255 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq255 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq255 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq255 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq283 : ∀ X0 X1 X2 X3 : G, (k (τ X3) (M.op X2 (M.op X0 X1))) = (τ (k X3 (σ (M.op (M.op X0 X1) X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X3 (M.op X2 (M.op X0 X1))
       have i₂ := eq217 X2 X0 X1
       grind)
    | (have i₁ := eq23 X0 (M.op (M.op X1 X2) X0)
       have i₂ := eq217 X0 X1 X2
       grind)
    | exact superpose eq217 eq23
    | exact resolve eq23 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq284 : ∀ X0 X1 X2 X3 : G, (k (M.op X2 (M.op X0 X1)) (τ X3)) = (τ (k (σ (M.op (M.op X0 X1) X2)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq29 (M.op X2 (M.op X0 X1)) X3
       have i₂ := eq217 X2 X0 X1
       grind)
    | (have i₁ := eq29 (M.op (M.op X1 X2) X0) X1
       have i₂ := eq217 X0 X1 X2
       grind)
    | exact superpose eq217 eq29
    | exact resolve eq29 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq290 : ∀ X0 X1 X2 X3 : G, (k (M.op X2 (M.op X0 X1)) (τ X3)) = (k (M.op (M.op X0 X1) X2) (τ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq284 X0 X1 X2 X3
       have i₂ := eq29 (M.op (M.op X0 X1) X2) X3
       grind)
    | exact superpose eq29 eq284
    | exact resolve eq284 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq291 : ∀ X0 X1 X2 X3 : G, (k (τ X3) (M.op X2 (M.op X0 X1))) = (k (τ X3) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq283 X0 X1 X2 X3
       have i₂ := eq23 X3 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq23 eq283
    | exact resolve eq283 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq302 : ∀ X0 X1 X2 X3 : G, (k (M.op X2 (M.op X0 X1)) (τ X3)) = (M.op (M.op (M.op X0 X1) X2) (τ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq290 X0 X1 X2 X3
       have i₂ := eq71 (M.op X0 X1) X2 (τ X3)
       grind)
    | exact superpose eq71 eq290
    | exact resolve eq290 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq306 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (τ X3)) = (M.op (M.op X2 (M.op X0 X1)) (τ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq302 X0 X1 X2 X3
       have i₂ := eq71 X2 (M.op X0 X1) (τ X3)
       grind)
    | exact superpose eq71 eq302
    | exact resolve eq302 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq562 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq252 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq252
    | (have j0 := eq252 (τ X0)
       grind)
    | exact resolve eq252 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq565 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq562 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq562
    | (have j0 := eq562 X0
       grind)
    | exact resolve eq562 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq569 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq565 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq565
    | (have j0 := eq565 X0
       grind)
    | exact resolve eq565 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq579 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k (σ (τ X0)) X1) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq256 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq256
    | (have j0 := eq256 (τ X0) X1
       grind)
    | exact resolve eq256 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq582 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k (σ (τ X0)) X1) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq579 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq579
    | (have j0 := eq579 X0 X1
       grind)
    | exact resolve eq579 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq586 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq582 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq582
    | (have j0 := eq582 X0 X1
       grind)
    | exact resolve eq582 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq594 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq569 (τ X0)
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq569
    | (have j0 := eq569 (τ X0)
       grind)
    | exact resolve eq569 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq602 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq586 (τ X0) X1
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq586
    | (have j0 := eq586 (τ X0) X1
       grind)
    | exact resolve eq586 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq612 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq257 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq257
    | (have j0 := eq257 (τ X0) X1
       grind)
    | exact resolve eq257 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq615 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq612 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq612
    | (have j0 := eq612 X0 X1
       grind)
    | exact resolve eq612 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq619 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq615 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq615
    | (have j0 := eq615 X0 X1
       grind)
    | exact resolve eq615 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq1143 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq236 X1 (τ X0)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq236
    | (have j0 := eq236 (τ X1) (τ X1)
       grind)
    | exact resolve eq236 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq1176 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1143 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1143
    | (have j0 := eq1143 X0 X1
       grind)
    | exact resolve eq1143 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq1319 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq235 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq1320 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1319 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319
  have eq1400 : ∀ X0 X1 X2 X3 : G, (k X0 (σ (M.op (M.op X2 X3) X1))) = (σ (k (τ X0) (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17 X0 (M.op (M.op X2 X3) X1)
       have i₂ := eq291 X2 X3 X1 X0
       grind)
    | (have i₁ := eq17 X3 (M.op X2 (M.op X0 X1))
       have i₂ := eq291 X0 X1 X2 X3
       grind)
    | exact superpose eq291 eq17
    | exact resolve eq17 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq1407 : ∀ X0 X1 X2 X3 : G, (k X0 (σ (M.op (M.op X2 X3) X1))) = (k X0 (σ (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1400 X0 X1 X2 X3
       have i₂ := eq17 X0 (M.op X1 (M.op X2 X3))
       grind)
    | exact superpose eq17 eq1400
    | exact resolve eq1400 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400
  have eq1743 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X3) X0) = (M.op (M.op X3 (M.op X1 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq306 X0 X1 X2 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq306
    | exact resolve eq306 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq1859 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 (M.op X1 X2)
       have i₂ := eq1743 (M.op (M.op X1 X2) X0) X1 X2 X0
       grind)
    | (have i₁ := eq9 (M.op X1 X2) x
       have i₂ := eq1743 (M.op x (M.op X1 X2)) X1 X2 x
       grind)
    | exact superpose eq1743 eq9
    | exact resolve eq9 eq1743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743
  have eq2345 : ∀ X0 X1 X2 : G, (M.op (σ X2) (k (σ (τ X0)) X1)) = (σ (k X2 (τ (k X0 X1)))) ∨ (k (σ (τ X0)) X1) = (M.op (k (σ (τ X0)) X1) (k (σ (τ X0)) X1)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq229 (τ X0) X1 X2
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq229
    | (have j0 := eq229 (τ X0) X1 X2
       grind)
    | exact resolve eq229 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq2395 : ∀ X0 X1 X2 : G, (M.op (σ X2) (k (σ (τ X0)) X1)) = (k (σ X2) (k X0 X1)) ∨ (k (σ (τ X0)) X1) = (M.op (k (σ (τ X0)) X1) (k (σ (τ X0)) X1)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2345 X0 X1 X2
       have i₂ := eq18 (k X0 X1) X2
       grind)
    | exact superpose eq18 eq2345
    | (have j0 := eq2345 X0 X1 X2
       grind)
    | exact resolve eq2345 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2345
  have eq2408 : ∀ X0 X1 X2 : G, (k (σ X2) (k X0 X1)) = (M.op (σ X2) (k X0 X1)) ∨ (k (σ (τ X0)) X1) = (M.op (k (σ (τ X0)) X1) (k (σ (τ X0)) X1)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2395 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2395
    | (have j0 := eq2395 X0 X1 X2
       grind)
    | exact resolve eq2395 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2395
  have eq2418 : ∀ X0 X1 X2 : G, (k (σ X2) (k X0 X1)) = (M.op (σ X2) (k X0 X1)) ∨ (k (σ (τ X0)) X1) = (M.op (k (σ (τ X0)) X1) (k (σ (τ X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2408 X0 X1 X2
       have j1 := eq12 (σ X2) (k X0 X1)
       grind)
    | (have r₁ := eq2408 X0 X1 X2
       have r₂ := eq12 (k (σ (τ X0)) X1) X1
       grind)
    | (have r₁ := eq2408 X0 X1 X2
       have r₂ := eq12 (σ X2) X1
       grind)
    | exact resolve eq2408 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2408
  have eq2419 : ∀ X0 X1 X2 : G, (k (σ X2) (k X0 X1)) = (M.op (σ X2) (k X0 X1)) ∨ (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2418 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2418
    | (have j0 := eq2418 X0 X1 X2
       grind)
    | exact resolve eq2418 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2418
  have eq3858 : ∀ X0 X1 X2 X3 : G, (σ (σ (M.op X0 (M.op X1 X2)))) ≠ (σ (k (σ (M.op X0 (M.op X1 X2))) (σ (M.op (M.op X1 X2) X0)))) ∨ (k X3 (σ (σ (M.op X0 (M.op X1 X2))))) = X3 ∨ (M.op X3 X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq257 (σ (M.op X0 (M.op X1 X2))) X3
       have i₂ := eq1407 (σ (M.op X0 (M.op X1 X2))) X0 X1 X2
       grind)
    | (have i₁ := eq257 (σ (M.op (M.op X2 X3) X1)) X1
       have i₂ := eq1407 (σ (M.op (M.op X2 X3) X1)) X1 X2 X3
       grind)
    | exact superpose eq1407 eq257
    | (have j0 := eq257 (σ (M.op X0 (M.op X1 X2))) X3
       grind)
    | exact resolve eq257 eq1407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257 eq1407
  have eq3902 : ∀ X0 X1 X2 X3 : G, (σ (σ (M.op X0 (M.op X1 X2)))) ≠ (σ (σ (k (M.op X0 (M.op X1 X2)) (M.op (M.op X1 X2) X0)))) ∨ (k X3 (σ (σ (M.op X0 (M.op X1 X2))))) = X3 ∨ (M.op X3 X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3858 X0 X1 X2 X3
       have i₂ := eq15 (M.op X0 (M.op X1 X2)) (M.op (M.op X1 X2) X0)
       grind)
    | exact superpose eq15 eq3858
    | (have j0 := eq3858 X0 X1 X2 X3
       grind)
    | exact resolve eq3858 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3858
  have eq3958 : ∀ X0 X1 X2 X3 : G, (σ (σ (M.op X0 (M.op X1 X2)))) ≠ (σ (σ (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X1 X2) X0)))) ∨ (k X3 (σ (σ (M.op X0 (M.op X1 X2))))) = X3 ∨ (M.op X3 X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3902 X0 X1 X2 X3
       have i₂ := eq71 X0 (M.op X1 X2) (M.op (M.op X1 X2) X0)
       grind)
    | exact superpose eq71 eq3902
    | (have j0 := eq3902 X0 X1 X2 X3
       grind)
    | exact resolve eq3902 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3902
  have eq3985 : ∀ X0 X1 X2 X3 : G, (σ (σ (M.op X0 (M.op X1 X2)))) ≠ (σ (σ (M.op X0 (M.op X1 X2)))) ∨ (k X3 (σ (σ (M.op X0 (M.op X1 X2))))) = X3 ∨ (M.op X3 X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3958 X0 X1 X2 X3
       have i₂ := eq1859 X0 X1 X2
       grind)
    | exact superpose eq1859 eq3958
    | (have j0 := eq3958 X0 X1 X2 X3
       grind)
    | exact resolve eq3958 eq1859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1859 eq3958
  have eq3986 : ∀ X0 X1 X2 X3 : G, (k X3 (σ (σ (M.op X0 (M.op X1 X2))))) = X3 ∨ (M.op X3 X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq3985 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3985
  have eq4039 : ∀ X0 X1 X2 : G, (k X2 (σ (σ (M.op X0 X1)))) = X2 ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3986 (M.op X1 X0) X1 X0 X2
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq3986
    | (have j0 := eq3986 X0 X1 X2 X2
       grind)
    | exact resolve eq3986 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3986
  have eq4337 : ∀ X0 X1 : G, (σ (σ (M.op X0 X1))) ≠ (σ (σ (M.op X0 X1))) ∨ (σ (σ (M.op X0 X1))) = (M.op (σ (σ (M.op X0 X1))) (σ (σ (M.op X0 X1)))) ∨ (σ (σ (M.op X0 X1))) = (M.op (σ (σ (M.op X0 X1))) (σ (σ (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq569 (σ (σ (M.op X0 X1)))
       have i₂ := eq4039 X0 X1 (σ (σ (M.op X0 X1)))
       grind)
    | exact superpose eq4039 eq569
    | (have j0 := eq569 (σ (σ (M.op X0 X1)))
       have j1 := eq4039 X0 X1 (σ (σ (M.op X0 X1)))
       grind)
    | (have r₁ := eq569 (σ (σ (M.op X0 X1)))
       have r₂ := eq4039 X0 X1 (σ (σ (M.op X0 X1)))
       grind)
    | exact resolve eq569 eq4039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq4338 : ∀ X0 X1 X2 : G, (σ (σ (M.op X0 X1))) ≠ (σ (σ (M.op X0 X1))) ∨ (k (σ (σ (M.op X0 X1))) X2) = (M.op (σ (σ (M.op X0 X1))) X2) ∨ (σ (σ (M.op X0 X1))) = (M.op (σ (σ (M.op X0 X1))) (σ (σ (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq586 (σ (σ (M.op X0 X1))) X2
       have i₂ := eq4039 X0 X1 (σ (σ (M.op X0 X1)))
       grind)
    | exact superpose eq4039 eq586
    | (have j0 := eq586 (σ (σ (M.op X0 X1))) X2
       have j1 := eq4039 X0 X1 (σ (σ (M.op X0 X1)))
       grind)
    | (have r₁ := eq586 (σ (σ (M.op X0 X1))) X1
       have r₂ := eq4039 X0 X1 (σ (σ (M.op X0 X1)))
       grind)
    | exact resolve eq586 eq4039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586 eq4039
  have eq4367 : ∀ X0 X1 X2 : G, (k (σ (σ (M.op X0 X1))) X2) = (M.op (σ (σ (M.op X0 X1))) X2) ∨ (σ (σ (M.op X0 X1))) = (M.op (σ (σ (M.op X0 X1))) (σ (σ (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4338 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4338
  have eq4368 : ∀ X0 X1 : G, (σ (σ (M.op X0 X1))) ≠ (σ (σ (M.op X0 X1))) ∨ (σ (σ (M.op X0 X1))) = (M.op (σ (σ (M.op X0 X1))) (σ (σ (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have j0 := eq4337 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4337
  have eq4369 : ∀ X0 X1 : G, (σ (σ (M.op X0 X1))) = (M.op (σ (σ (M.op X0 X1))) (σ (σ (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have j0 := eq4368 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4368
  have eq4389 : ∀ X0 X1 X2 : G, (k (σ (σ (M.op X0 X1))) X2) = (M.op (σ (σ (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4367 X0 X1 X2
       have j1 := eq12 (σ (σ (M.op X0 X1))) X2
       grind)
    | (have r₁ := eq4367 X0 X1 X2
       have r₂ := eq12 (σ (σ (M.op X0 X1))) X1
       grind)
    | exact resolve eq4367 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4367
  have eq4679 : ∀ X0 X1 : G, (τ (σ (σ (M.op X0 X1)))) ≠ (τ (M.op (σ (σ (M.op X0 X1))) (σ (σ (M.op X0 X1))))) ∨ (τ (σ (σ (M.op X0 X1)))) = (M.op (τ (σ (σ (M.op X0 X1)))) (τ (σ (σ (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq594 (σ (σ (M.op X0 X1)))
       have i₂ := eq4389 X0 X1 (σ (σ (M.op X0 X1)))
       grind)
    | exact superpose eq4389 eq594
    | (have j0 := eq594 (σ (σ (M.op X0 X1)))
       grind)
    | exact resolve eq594 eq4389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq4680 : ∀ X0 X1 X2 : G, (τ (σ (σ (M.op X0 X1)))) ≠ (τ (M.op (σ (σ (M.op X0 X1))) (σ (σ (M.op X0 X1))))) ∨ (k (τ (σ (σ (M.op X0 X1)))) X2) = (M.op (τ (σ (σ (M.op X0 X1)))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq602 (σ (σ (M.op X0 X1))) X2
       have i₂ := eq4389 X0 X1 (σ (σ (M.op X0 X1)))
       grind)
    | exact superpose eq4389 eq602
    | (have j0 := eq602 (σ (σ (M.op X0 X1))) X2
       grind)
    | exact resolve eq602 eq4389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602 eq4389
  have eq4730 : ∀ X0 X1 X2 : G, (τ (σ (σ (M.op X0 X1)))) ≠ (τ (σ (σ (M.op X0 X1)))) ∨ (k (τ (σ (σ (M.op X0 X1)))) X2) = (M.op (τ (σ (σ (M.op X0 X1)))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4680 X0 X1 X2
       have i₂ := eq4369 X0 X1
       grind)
    | exact superpose eq4369 eq4680
    | (have j0 := eq4680 X0 X1 X2
       grind)
    | exact resolve eq4680 eq4369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4680
  have eq4731 : ∀ X0 X1 X2 : G, (k (τ (σ (σ (M.op X0 X1)))) X2) = (M.op (τ (σ (σ (M.op X0 X1)))) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4730 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4730
  have eq4732 : ∀ X0 X1 : G, (τ (σ (σ (M.op X0 X1)))) ≠ (τ (σ (σ (M.op X0 X1)))) ∨ (τ (σ (σ (M.op X0 X1)))) = (M.op (τ (σ (σ (M.op X0 X1)))) (τ (σ (σ (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq4679 X0 X1
       have i₂ := eq4369 X0 X1
       grind)
    | exact superpose eq4369 eq4679
    | (have j0 := eq4679 X0 X1
       grind)
    | exact resolve eq4679 eq4369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4369 eq4679
  have eq4733 : ∀ X0 X1 : G, (τ (σ (σ (M.op X0 X1)))) = (M.op (τ (σ (σ (M.op X0 X1)))) (τ (σ (σ (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have j0 := eq4732 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4732
  have eq4763 : ∀ X0 X1 X2 : G, (k (σ (M.op X0 X1)) X2) = (M.op (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4731 X0 X1 X2
       have i₂ := eq10 (σ (M.op X0 X1))
       grind)
    | exact superpose eq10 eq4731
    | exact resolve eq4731 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4731
  have eq4764 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4733 X0 X1
       have i₂ := eq10 (σ (M.op X0 X1))
       grind)
    | exact superpose eq10 eq4733
    | exact resolve eq4733 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4733
  have eq4825 : ∀ X0 X1 X2 : G, (σ (k (M.op X0 X1) X2)) = (M.op (σ (M.op X0 X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (M.op X0 X1) X2
       have i₂ := eq4763 X0 X1 (σ X2)
       grind)
    | exact superpose eq4763 eq15
    | exact resolve eq15 eq4763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4895 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) X2)) = (M.op (σ (M.op X0 X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4825 X0 X1 X2
       have i₂ := eq71 X0 X1 X2
       grind)
    | exact superpose eq71 eq4825
    | exact resolve eq4825 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4825
  have eq5675 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X1 X2) (τ X0))) = (M.op (σ (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4895 X1 X2 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4895
    | exact resolve eq4895 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5704 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (σ (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4764 X0 X1
       have i₂ := eq4895 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq4895 eq4764
    | exact resolve eq4764 eq4895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4764
  have eq5765 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5704 X0 X1
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq5704
    | exact resolve eq5704 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5704
  have eq5891 : ∀ X0 X1 X2 : G, (k (σ (M.op X0 X1)) (σ X2)) = (σ (k (M.op X1 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (M.op X1 X0) X2
       have i₂ := eq5765 X1 X0
       grind)
    | (have i₁ := eq15 (M.op X1 X0) X2
       have i₂ := eq5765 X0 X1
       grind)
    | exact superpose eq5765 eq15
    | exact resolve eq15 eq5765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5897 : ∀ X0 X1 X2 : G, (τ (k X2 (σ (M.op X0 X1)))) = (k (τ X2) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X2 (M.op X1 X0)
       have i₂ := eq5765 X1 X0
       grind)
    | (have i₁ := eq23 X2 (M.op X1 X0)
       have i₂ := eq5765 X0 X1
       grind)
    | exact superpose eq5765 eq23
    | exact resolve eq23 eq5765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5902 : ∀ X0 X1 X2 : G, (τ (k (σ (M.op X0 X1)) X2)) = (k (M.op X1 X0) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 (M.op X1 X0) X2
       have i₂ := eq5765 X1 X0
       grind)
    | (have i₁ := eq29 (M.op X1 X0) X2
       have i₂ := eq5765 X0 X1
       grind)
    | exact superpose eq5765 eq29
    | exact resolve eq29 eq5765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5925 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (τ X2)) = (τ (k (σ (M.op X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5902 X0 X1 X2
       have i₂ := eq71 X1 X0 (τ X2)
       grind)
    | exact superpose eq71 eq5902
    | exact resolve eq5902 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5902
  have eq5930 : ∀ X0 X1 X2 : G, (k (τ X2) (M.op X0 X1)) = (k (τ X2) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5897 X0 X1 X2
       have i₂ := eq23 X2 (M.op X0 X1)
       grind)
    | exact superpose eq23 eq5897
    | exact resolve eq5897 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq5897
  have eq5936 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X1 X0) X2)) = (k (σ (M.op X0 X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5891 X0 X1 X2
       have i₂ := eq71 X1 X0 X2
       grind)
    | exact superpose eq71 eq5891
    | exact resolve eq5891 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5891
  have eq5960 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) (τ X2)) = (M.op (M.op X1 X0) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5925 X0 X1 X2
       have i₂ := eq29 (M.op X0 X1) X2
       grind)
    | exact superpose eq29 eq5925
    | exact resolve eq5925 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5925
  have eq5965 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X1 X0) X2)) = (σ (k (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5936 X0 X1 X2
       have i₂ := eq15 (M.op X0 X1) X2
       grind)
    | exact superpose eq15 eq5936
    | exact resolve eq5936 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5936
  have eq5976 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (τ X2)) = (M.op (M.op X1 X0) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5960 X0 X1 X2
       have i₂ := eq71 X0 X1 (τ X2)
       grind)
    | exact superpose eq71 eq5960
    | exact resolve eq5960 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5960
  have eq5981 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) X2)) = (σ (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5965 X1 X0 X2
       have i₂ := eq71 X1 X0 X2
       grind)
    | exact superpose eq71 eq5965
    | exact resolve eq5965 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5965
  have eq6222 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X2)) = (k X0 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5930 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5930
    | exact resolve eq5930 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5930
  have eq6384 : ∀ X0 X1 X2 : G, (τ (k (σ X0) (M.op X1 X2))) = (k X0 (τ (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 X0 (M.op X2 X1)
       have i₂ := eq6222 (σ X0) X2 X1
       grind)
    | (have i₁ := eq29 X0 (M.op X2 X1)
       have i₂ := eq6222 (σ X0) X1 X2
       grind)
    | exact superpose eq6222 eq29
    | exact resolve eq29 eq6222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6222
  have eq6411 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 X2))) = (k X0 (τ (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6384 X0 X1 X2
       have i₂ := eq29 X0 (M.op X1 X2)
       grind)
    | exact superpose eq29 eq6384
    | exact resolve eq6384 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq6384
  have eq6816 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X2 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5976 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5976
    | exact resolve eq5976 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5976
  have eq7396 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq6816 (M.op X1 X0) X1 X0
       grind)
    | (have i₁ := eq9 X0 X1
       have i₂ := eq6816 (M.op X1 X0) X0 X1
       grind)
    | exact superpose eq6816 eq9
    | exact resolve eq9 eq6816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6816
  have eq9708 : ∀ X0 X1 X2 : G, (k (σ (M.op X0 X1)) X2) = (σ (M.op (M.op X1 X0) (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5981 X1 X0 (τ X2)
       have i₂ := eq89 X0 X1 X2
       grind)
    | exact superpose eq89 eq5981
    | exact resolve eq5981 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq5981
  have eq9848 : ∀ X0 X1 X2 : G, (k (σ (M.op X0 X1)) X2) = (M.op (σ (M.op X1 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9708 X0 X1 X2
       have i₂ := eq5675 X2 X1 X0
       grind)
    | exact superpose eq5675 eq9708
    | exact resolve eq9708 eq5675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5675 eq9708
  have eq11028 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X1)) X2) = (M.op (σ (M.op X1 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4763 X1 X0 X2
       have i₂ := eq9848 X1 X0 X2
       grind)
    | exact superpose eq9848 eq4763
    | exact resolve eq4763 eq9848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4763 eq9848
  have eq11775 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) ≠ (k (τ (M.op X0 X1)) (τ (M.op X1 X0))) ∨ (k X2 (τ (M.op X0 X1))) = X2 ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq619 (τ (M.op X0 X1)) X2
       have i₂ := eq6411 (τ (M.op X0 X1)) X0 X1
       grind)
    | (have i₁ := eq619 (τ (M.op X0 X1)) X2
       have i₂ := eq6411 (τ (M.op X0 X1)) X1 X0
       grind)
    | exact superpose eq6411 eq619
    | (have j0 := eq619 (τ (M.op X0 X1)) X2
       grind)
    | exact resolve eq619 eq6411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619 eq6411
  have eq11841 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) ≠ (τ (k (M.op X0 X1) (M.op X1 X0))) ∨ (k X2 (τ (M.op X0 X1))) = X2 ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11775 X0 X1 X2
       have i₂ := eq33 (M.op X1 X0) (M.op X0 X1)
       grind)
    | exact superpose eq33 eq11775
    | (have j0 := eq11775 X0 X1 X2
       grind)
    | exact resolve eq11775 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq11775
  have eq11943 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) ≠ (τ (M.op (M.op X0 X1) (M.op X1 X0))) ∨ (k X2 (τ (M.op X0 X1))) = X2 ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11841 X0 X1 X2
       have i₂ := eq71 X0 X1 (M.op X1 X0)
       grind)
    | exact superpose eq71 eq11841
    | (have j0 := eq11841 X0 X1 X2
       grind)
    | exact resolve eq11841 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq11841
  have eq11992 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) ≠ (τ (M.op X0 X1)) ∨ (k X2 (τ (M.op X0 X1))) = X2 ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11943 X0 X1 X2
       have i₂ := eq7396 X0 X1
       grind)
    | exact superpose eq7396 eq11943
    | (have j0 := eq11943 X0 X1 X2
       grind)
    | exact resolve eq11943 eq7396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7396 eq11943
  have eq11993 : ∀ X0 X1 X2 : G, (k X2 (τ (M.op X0 X1))) = X2 ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq11992 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11992
  have eq13088 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X1)) X2) = (M.op X2 (σ (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X2 (σ (M.op X1 X0))
       have i₂ := eq11028 X1 X0 X2
       grind)
    | (have i₁ := eq67 X2 (σ (M.op X1 X0))
       have i₂ := eq11028 X0 X1 X2
       grind)
    | exact superpose eq11028 eq67
    | exact resolve eq67 eq11028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq11028
  have eq15132 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ (M.op X1 X2))) = (σ (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4895 X2 X1 X0
       have i₂ := eq13088 X2 X1 (σ X0)
       grind)
    | (have i₁ := eq4895 X0 X1 (M.op X1 X0)
       have i₂ := eq13088 X0 X1 (σ (M.op X0 X1))
       grind)
    | exact superpose eq13088 eq4895
    | exact resolve eq4895 eq13088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4895 eq13088
  have eq22576 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (k (σ (τ X0)) X0) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1320 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1320
    | (have j0 := eq1320 (τ X0)
       grind)
    | exact resolve eq1320 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320
  have eq22724 : ∀ X0 : G, (M.op X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq22576 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22576
    | (have j0 := eq22576 X0
       grind)
    | exact resolve eq22576 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22576
  have eq22745 : ∀ X0 : G, (M.op X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq22724 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22724
    | (have j0 := eq22724 X0
       grind)
    | exact resolve eq22724 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22724
  have eq125839 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1176 X0 (σ X0)
       have i₂ := eq22745 (σ X0)
       grind)
    | exact superpose eq22745 eq1176
    | (have j0 := eq1176 X0 (σ X0)
       have j1 := eq22745 (σ X0)
       grind)
    | exact resolve eq1176 eq22745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176 eq22745
  have eq126034 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq125839 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125839
  have eq126042 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq126034 X0
       have j1 := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq126034 X0
       have r₂ := eq12 (σ X0) x
       grind)
    | exact resolve eq126034 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126034
  have eq126056 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq126042 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq126042
    | exact resolve eq126042 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126042
  have eq127003 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq126056 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq126056
    | exact resolve eq126056 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127235 : ∀ X0 X1 : G, (k X1 (τ (σ (k X0 X0)))) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11993 (σ X0) (σ X0) X1
       have i₂ := eq126056 X0
       grind)
    | exact superpose eq126056 eq11993
    | (have j0 := eq11993 X0 X1 X1
       grind)
    | exact resolve eq11993 eq126056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11993
  have eq127364 : ∀ X0 X1 : G, (k X1 (k X0 X0)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq127235 X0 X1
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq127235
    | (have j0 := eq127235 X0 X1
       grind)
    | exact resolve eq127235 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127235
  have eq127471 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq127003 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq127003
    | exact resolve eq127003 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq127003
  have eq127599 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq127471 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq127471
    | exact resolve eq127471 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127471
  have eq538043 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2419 X1 (k X0 X0) x
       have i₂ := eq127364 X0 X1
       grind)
    | exact superpose eq127364 eq2419
    | (have j1 := eq127364 X0 X0
       grind)
    | exact resolve eq2419 eq127364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2419 eq127364
  have eq538308 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq538043 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538043
  have eq538640 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq538308 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq538308
    | (have j0 := eq538308 X1 X1
       grind)
    | exact resolve eq538308 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq538862 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq538308 (σ X1) X0
       grind)
    | exact superpose eq538308 eq15
    | (have j1 := eq538308 (σ X1) X1
       grind)
    | exact resolve eq15 eq538308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538308
  have eq539293 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq538862 X0 X1
       have i₂ := eq126056 X1
       grind)
    | exact superpose eq126056 eq538862
    | (have j0 := eq538862 X0 X1
       grind)
    | exact resolve eq538862 eq126056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126056 eq538862
  have eq539374 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq539293 X0 X1
       have i₂ := eq127599 X1
       grind)
    | exact superpose eq127599 eq539293
    | (have j0 := eq539293 X0 X1
       grind)
    | exact resolve eq539293 eq127599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127599 eq539293
  have eq540093 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq538640 (τ X0) X1
       grind)
    | exact superpose eq538640 eq17
    | (have j1 := eq538640 X0 X1
       grind)
    | exact resolve eq17 eq538640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq538640
  have eq545926 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq540093 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq540093
    | (have j0 := eq540093 X0 X1
       grind)
    | exact resolve eq540093 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540093
  have eq546596 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq545926 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq545926
    | (have j0 := eq545926 X0 X1
       grind)
    | exact resolve eq545926 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545926
  have eq1492813 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq539374 X1 X0
       grind)
    | exact superpose eq539374 eq10
    | (have j1 := eq539374 X1 X0
       grind)
    | exact resolve eq10 eq539374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539374
  have eq1493298 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1492813 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1492813
    | (have j0 := eq1492813 X0 X1
       grind)
    | exact resolve eq1492813 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1492813
  have eq1494850 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1493298 y x
       grind)
    | exact superpose eq1493298 eq16
    | (have j1 := eq1493298 y x
       grind)
    | exact resolve eq16 eq1493298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493298
  have eq1496262 : y = (M.op y y) := by
    first
    | (have j1 := eq546596 x y
       grind)
    | (have r₁ := eq1494850
       have r₂ := eq546596 x y
       grind)
    | exact resolve eq1494850 eq546596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546596 eq1494850
  have eq1506323 : ∀ X0 : G, (σ (M.op y X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15132 X0 y y
       have i₂ := eq1496262
       grind)
    | exact superpose eq1496262 eq15132
    | exact resolve eq15132 eq1496262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15132 eq1496262
  have eq1563941 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1506323 x
       grind)
    | exact superpose eq1506323 eq16
    | exact resolve eq16 eq1506323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1506323
  have eq1565698 : False := by grind
  exact eq1565698

/-- `Equation3798`: `x ◇ y = (z ◇ x) ◇ (w ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,Y) else if m(X,Y) = Y then m(X,X) else m(Y,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pyy_pxx_pyy_Equation3798 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) Law3798 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3798.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17
    | exact resolve eq17 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq44 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X2 X1) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq9 (M.op X2 X1) X3 (M.op x X0) X5
       have i₂ := eq9 X0 X1 x X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 X3 X4 X5 : G, (M.op X4 (M.op X1 X3)) = (M.op (M.op X5 X4) (M.op X0 X3)) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op X1 X3) X5 (M.op x X0)
       have i₂ := eq9 X0 X3 x X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X1 X3 X4 : G, (M.op X4 (M.op X1 X3)) = (M.op X4 X3) := by
    intro X1 X3 X4
    first
    | (have i₁ := eq45 x X1 X3 X4 x
       have i₂ := eq9 X4 X3 x x
       grind)
    | exact superpose eq9 eq45
    | exact resolve eq45 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq47 : ∀ X1 X2 X3 : G, (M.op X1 X3) = (M.op (M.op X2 X1) X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq44 x X1 X2 X3 x
       have i₂ := eq9 X1 X3 x x
       grind)
    | exact superpose eq9 eq44
    | exact resolve eq44 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq67 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ X2 ∨ (k X2 (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 X1)
       have i₂ := eq47 X1 X0 X2
       grind)
    | exact superpose eq47 eq12
    | (have j0 := eq12 X2 X1
       grind)
    | exact resolve eq12 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ X2 ∨ (M.op X1 X1) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X0 X1 X2
       have i₂ := eq9 X1 X1 X0 X0
       grind)
    | exact superpose eq9 eq67
    | (have j0 := eq67 X0 X1 X2
       grind)
    | (have r₁ := eq67 X0 (M.op X2 X0) (M.op X0 X1)
       have r₂ := eq9 X0 X1 X2 X0
       grind)
    | exact resolve eq67 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) ≠ (M.op X0 X2) ∨ (M.op X0 X0) = (k (M.op X1 X2) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq68 X3 X0 (M.op X1 X2)
       have i₂ := eq46 X1 X2 X0
       grind)
    | exact superpose eq46 eq68
    | (have j0 := eq68 X3 X0 (M.op X1 X2)
       grind)
    | (have r₁ := eq68 X0 x (M.op x X3)
       have r₂ := eq46 x X3 x
       grind)
    | exact resolve eq68 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq82 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (M.op X0 X2) ∨ (M.op (M.op X1 X2) X0) = X0 ∨ (M.op X0 X0) = (k X0 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X1 X2)
       have i₂ := eq46 X1 X2 X0
       grind)
    | exact superpose eq46 eq13
    | (have j0 := eq13 X0 (M.op X1 X2)
       grind)
    | (have r₁ := eq13 x (M.op x x)
       have r₂ := eq46 x x x
       grind)
    | exact resolve eq13 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (M.op X0 X2) ∨ (M.op X2 X0) = X0 ∨ (M.op X0 X0) = (k X0 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq82 X0 X1 X2
       have i₂ := eq47 X2 X1 X0
       grind)
    | exact superpose eq47 eq82
    | (have j0 := eq82 X0 X1 X2
       grind)
    | (have r₁ := eq82 (M.op X2 X1) X1 x
       have r₂ := eq47 X1 X2 x
       grind)
    | (have r₁ := eq82 X1 (M.op X2 X1) x
       have r₂ := eq47 X1 X2 x
       grind)
    | exact resolve eq82 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq87 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k (τ X1) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq87 X1 X0
       grind)
    | exact superpose eq87 eq23
    | (have j1 := eq87 X1 X0
       grind)
    | exact resolve eq23 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq87 X1 X0
       grind)
    | exact superpose eq87 eq15
    | (have j1 := eq87 X1 X0
       grind)
    | exact resolve eq15 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq93 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq89 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq89 X0 X1
       grind)
    | exact resolve eq12 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq99 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq125 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq99 X1 X0
       grind)
    | exact superpose eq99 eq15
    | (have j1 := eq99 X0 X1
       grind)
    | exact resolve eq15 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq162 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k (M.op X0 X1) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq69 X0 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq185 : ∀ X0 X1 X2 : G, (τ (M.op X1 X1)) = (k (τ (M.op X1 X2)) (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 (M.op X0 X1) (M.op X1 X2)
       have i₂ := eq162 X1 X2 X0
       grind)
    | exact superpose eq162 eq23
    | exact resolve eq23 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq204 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 X2)) (τ X0)) ∨ (k (τ X1) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq185 X1 X0 X2
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq185
    | (have j1 := eq88 X0 (M.op X0 X2)
       grind)
    | exact resolve eq185 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq185
  have eq216 : ∀ X0 X2 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 X2)) (τ X0)) := by
    intro X0 X2
    first
    | (have j0 := eq204 X0 (M.op X0 X2) X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq258 : ∀ X0 X1 : G, (σ (τ (M.op X1 X1))) = (k (σ (τ (M.op X1 X0))) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ (M.op X1 X0)) (τ X1)
       have i₂ := eq216 X1 X0
       grind)
    | exact superpose eq216 eq15
    | exact resolve eq15 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq259 : ∀ X0 X1 : G, (σ (τ (M.op X1 X1))) = (k (σ (τ (M.op X1 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq258 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq258
    | exact resolve eq258 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq264 : ∀ X0 X1 : G, (σ (τ (M.op X1 X1))) = (k (M.op X1 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq259 X0 X1
       have i₂ := eq11 (M.op X1 X0)
       grind)
    | exact superpose eq11 eq259
    | exact resolve eq259 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq269 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq264 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq264
    | exact resolve eq264 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq1541 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq85 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq1558 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (τ (M.op X1 X1)) = (k (τ X1) (τ (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (M.op X1 X0) X1
       have i₂ := eq1541 X0 X1
       grind)
    | exact superpose eq1541 eq23
    | (have j1 := eq1541 X0 X1
       grind)
    | exact resolve eq23 eq1541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1541
  have eq5739 : ∀ X0 : G, (k (σ X0) (σ X0)) ≠ (k (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq125 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq5740 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq5739 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5739
  have eq5806 : ∀ X0 X1 : G, (σ (M.op X1 (M.op X0 X1))) = (k (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5740 (M.op X0 X1)
       have i₂ := eq47 X1 X0 (M.op X0 X1)
       grind)
    | exact superpose eq47 eq5740
    | exact resolve eq5740 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5851 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq5740 X0
       grind)
    | exact superpose eq5740 eq10
    | exact resolve eq10 eq5740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5855 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq5851 X0
       have i₂ := eq17 X0 X0
       grind)
    | exact superpose eq17 eq5851
    | exact resolve eq5851 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq5851
  have eq5874 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (k (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5806 X0 X1
       have i₂ := eq46 X0 X1 X1
       grind)
    | (have i₁ := eq5806 X0 x
       have i₂ := eq46 X1 (M.op X0 x) x
       grind)
    | exact superpose eq46 eq5806
    | exact resolve eq5806 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5806
  have eq5878 : ∀ X0 X1 : G, (k (σ (M.op X0 X1)) (σ (M.op X0 X1))) = (k (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5874 X0 X1
       have i₂ := eq5740 X1
       grind)
    | exact superpose eq5740 eq5874
    | exact resolve eq5874 eq5740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5874
  have eq5894 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0 X0
       have i₂ := eq5855 X0
       grind)
    | exact superpose eq5855 eq23
    | exact resolve eq23 eq5855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq5900 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq5894 X0
       have i₂ := eq5855 (τ X0)
       grind)
    | exact superpose eq5855 eq5894
    | exact resolve eq5894 eq5855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5894
  have eq5914 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) = (τ (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5900 (M.op X0 X1)
       have i₂ := eq47 X1 X0 (M.op X0 X1)
       grind)
    | exact superpose eq47 eq5900
    | exact resolve eq5900 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5983 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5914 X0 X1
       have i₂ := eq46 X0 X1 X1
       grind)
    | (have i₁ := eq5914 X0 x
       have i₂ := eq46 X1 (M.op X0 x) x
       grind)
    | exact superpose eq46 eq5914
    | exact resolve eq5914 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5914
  have eq5998 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5983 X0 X1
       have i₂ := eq5900 X1
       grind)
    | exact superpose eq5900 eq5983
    | exact resolve eq5983 eq5900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5983
  have eq6348 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (k (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5878 X0 X1
       have i₂ := eq5855 (σ X1)
       grind)
    | exact superpose eq5855 eq5878
    | exact resolve eq5878 eq5855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5878
  have eq6349 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6348 X0 X1
       have i₂ := eq5855 (σ (M.op X0 X1))
       grind)
    | exact superpose eq5855 eq6348
    | exact resolve eq6348 eq5855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6348
  have eq6362 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 X1))) = (M.op X2 (M.op (σ X1) (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46 (σ (M.op X0 X1)) (σ (M.op X0 X1)) X2
       have i₂ := eq6349 X0 X1
       grind)
    | exact superpose eq6349 eq46
    | exact resolve eq46 eq6349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6363 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X1)) X2) = (M.op (M.op (σ X1) (σ X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47 (σ (M.op X0 X1)) (σ (M.op X0 X1)) X2
       have i₂ := eq6349 X0 X1
       grind)
    | exact superpose eq6349 eq47
    | exact resolve eq47 eq6349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6349
  have eq6410 : ∀ X0 X1 X2 : G, (M.op (σ X1) X2) = (M.op (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6363 X0 X1 X2
       have i₂ := eq47 (σ X1) (σ X1) X2
       grind)
    | exact superpose eq47 eq6363
    | exact resolve eq6363 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6363
  have eq6411 : ∀ X0 X1 X2 : G, (M.op X2 (σ X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6362 X0 X1 X2
       have i₂ := eq46 (σ X1) (σ X1) X2
       grind)
    | (have i₁ := eq6362 X0 X1 x
       have i₂ := eq46 X1 (M.op (σ X1) (σ X1)) x
       grind)
    | exact superpose eq46 eq6362
    | exact resolve eq6362 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6362
  have eq6577 : ∀ X0 X1 X2 : G, (σ (M.op X1 X2)) = (M.op X0 (σ X2)) ∨ (τ (M.op (σ (M.op X1 X2)) (σ (M.op X1 X2)))) = (k (τ (σ (M.op X1 X2))) (τ (M.op (σ (M.op X1 X2)) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1558 X0 (σ (M.op X1 X2))
       have i₂ := eq6411 X1 X2 X0
       grind)
    | exact superpose eq6411 eq1558
    | (have j0 := eq1558 X0 (σ (M.op X1 X2))
       grind)
    | exact resolve eq1558 eq6411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1558
  have eq6598 : ∀ X0 X1 X2 : G, (τ (M.op (σ (M.op X1 X2)) (σ (M.op X1 X2)))) = (k (τ (σ (M.op X1 X2))) (τ (M.op (σ X2) X0))) ∨ (σ (M.op X1 X2)) = (M.op X0 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6577 X0 X1 X2
       have i₂ := eq6410 X1 X2 X0
       grind)
    | exact superpose eq6410 eq6577
    | (have j0 := eq6577 X0 X1 X2
       grind)
    | exact resolve eq6577 eq6410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6410 eq6577
  have eq6631 : ∀ X0 X1 X2 : G, (τ (M.op (σ (M.op X1 X2)) (σ (M.op X1 X2)))) = (k (M.op X1 X2) (τ (M.op (σ X2) X0))) ∨ (σ (M.op X1 X2)) = (M.op X0 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6598 X0 X1 X2
       have i₂ := eq10 (M.op X1 X2)
       grind)
    | exact superpose eq10 eq6598
    | (have j0 := eq6598 X0 X1 X2
       grind)
    | exact resolve eq6598 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6598
  have eq6647 : ∀ X0 X1 X2 : G, (M.op (τ (σ (M.op X1 X2))) (τ (σ (M.op X1 X2)))) = (k (M.op X1 X2) (τ (M.op (σ X2) X0))) ∨ (σ (M.op X1 X2)) = (M.op X0 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6631 X0 X1 X2
       have i₂ := eq5900 (σ (M.op X1 X2))
       grind)
    | exact superpose eq5900 eq6631
    | (have j0 := eq6631 X0 X1 X2
       grind)
    | exact resolve eq6631 eq5900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5900 eq6631
  have eq6656 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 X2)) = (k (M.op X1 X2) (τ (M.op (σ X2) X0))) ∨ (σ (M.op X1 X2)) = (M.op X0 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6647 X0 X1 X2
       have i₂ := eq10 (M.op X1 X2)
       grind)
    | exact superpose eq10 eq6647
    | (have j0 := eq6647 X0 X1 X2
       grind)
    | exact resolve eq6647 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6647
  have eq6664 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k (M.op X1 X2) (τ (M.op (σ X2) X0))) ∨ (σ (M.op X1 X2)) = (M.op X0 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6656 X0 X1 X2
       have i₂ := eq9 X2 X2 X1 X1
       grind)
    | exact superpose eq9 eq6656
    | (have j0 := eq6656 X0 X1 X2
       grind)
    | exact resolve eq6656 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6656
  have eq7182 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 X1)) X2) = (M.op (M.op (τ X1) (τ X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47 (τ (M.op X0 X1)) (τ (M.op X0 X1)) X2
       have i₂ := eq5998 X0 X1
       grind)
    | exact superpose eq5998 eq47
    | exact resolve eq47 eq5998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7220 : ∀ X0 X1 X2 : G, (M.op (τ X1) X2) = (M.op (τ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7182 X0 X1 X2
       have i₂ := eq47 (τ X1) (τ X1) X2
       grind)
    | exact superpose eq47 eq7182
    | exact resolve eq7182 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq7182
  have eq7310 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X1 X2)) (τ (M.op X1 X2))) = (k (M.op (τ X2) X0) (τ (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq269 X0 (τ (M.op X1 X2))
       have i₂ := eq7220 X1 X2 X0
       grind)
    | exact superpose eq7220 eq269
    | exact resolve eq269 eq7220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq7220
  have eq7341 : ∀ X0 X1 X2 : G, (M.op (τ X2) (τ X2)) = (k (M.op (τ X2) X0) (τ (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7310 X0 X1 X2
       have i₂ := eq5998 X1 X2
       grind)
    | exact superpose eq5998 eq7310
    | exact resolve eq7310 eq5998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5998 eq7310
  have eq8585 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k (M.op X0 X1) (τ (M.op X2 (σ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7341 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7341
    | exact resolve eq7341 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7341
  have eq179294 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6664 (σ X1) X1 X0
       have i₂ := eq8585 X1 X0 (σ X0)
       grind)
    | exact superpose eq8585 eq6664
    | (have j0 := eq6664 (σ X1) X1 X0
       grind)
    | exact resolve eq6664 eq8585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6664 eq8585
  have eq180010 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq179294 y x
       grind)
    | exact superpose eq179294 eq16
    | (have j1 := eq179294 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq179294 y x
       grind)
    | exact resolve eq16 eq179294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179294
  have eq180126 : (M.op y y) = (M.op x x) := by grind
  clear eq180010
  have eq180623 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq46 y y X0
       have i₂ := eq180126
       grind)
    | exact superpose eq180126 eq46
    | exact resolve eq46 eq180126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180126
  have eq180794 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq180623 X0
       have i₂ := eq46 x x X0
       grind)
    | (have i₁ := eq180623 x
       have i₂ := eq46 x (M.op x x) x
       grind)
    | exact superpose eq46 eq180623
    | exact resolve eq180623 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq180623
  have eq181698 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X1 (σ (M.op X0 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq6411 X0 y X1
       have i₂ := eq180794 X0
       grind)
    | exact superpose eq180794 eq6411
    | exact resolve eq6411 eq180794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182131 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq180794 x
       grind)
    | exact superpose eq180794 eq16
    | exact resolve eq16 eq180794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180794
  have eq182132 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq182131
       have i₂ := eq5740 x
       grind)
    | exact superpose eq5740 eq182131
    | exact resolve eq182131 eq5740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5740 eq182131
  have eq182293 : ∀ X1 : G, (M.op X1 (σ y)) = (M.op X1 (σ x)) := by
    intro X1
    first
    | (have i₁ := eq181698 x X1
       have i₂ := eq6411 x x X1
       grind)
    | exact superpose eq6411 eq181698
    | exact resolve eq181698 eq6411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6411 eq181698
  have eq182344 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq182132
       have i₂ := eq5855 (σ x)
       grind)
    | exact superpose eq5855 eq182132
    | exact resolve eq182132 eq5855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5855 eq182132
  have eq191136 : False := by grind
  exact eq191136

/-- `Equation3867`: `x ◇ x = (x ◇ (y ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation3867 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3867 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3867.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
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
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X2 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq24
    | exact resolve eq24 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq24
    | (have j1 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq24 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq283 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq347 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq348 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq347 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq355 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq20 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq348 (τ X0)
       grind)
    | exact superpose eq348 eq20
    | exact resolve eq20 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1034 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq286 x y
       grind)
    | exact superpose eq286 eq16
    | (have j1 := eq286 x y
       grind)
    | exact resolve eq16 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1037 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (M.op (σ X0) (σ (k X0 X1))) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X1)
       have i₂ := eq286 X1 X0
       grind)
    | exact superpose eq286 eq9
    | (have j1 := eq286 X1 X0
       grind)
    | exact resolve eq9 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1040 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq1042 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq286 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1043 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1042 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq1045 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1040 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040
  have eq1050 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1045 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq1045
    | (have j0 := eq1045 X0
       grind)
    | exact resolve eq1045 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq2572 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k (τ X0) (k (τ X0) (τ X0)))) = (M.op X0 (σ (k (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq1050 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1050
    | exact resolve eq1050 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050
  have eq2603 : ∀ X0 : G, (σ (k (τ X0) (k (τ X0) (τ X0)))) = (M.op X0 (k (σ (τ X0)) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2572 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq2572
    | (have j0 := eq2572 X0
       grind)
    | exact resolve eq2572 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2572
  have eq2606 : ∀ X0 : G, (σ (k (τ X0) (k (τ X0) (τ X0)))) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2603 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2603
    | (have j0 := eq2603 X0
       grind)
    | exact resolve eq2603 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2603
  have eq2607 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2606 X0
       have i₂ := eq19 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq19 eq2606
    | (have j0 := eq2606 X0
       grind)
    | exact resolve eq2606 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2606
  have eq2608 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k X0 (k (σ (τ X0)) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2607 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq2607
    | (have j0 := eq2607 X0
       grind)
    | exact resolve eq2607 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2607
  have eq2609 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2608 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2608
    | (have j0 := eq2608 X0
       grind)
    | exact resolve eq2608 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2608
  have eq2612 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq2609 X0
       grind)
    | exact superpose eq2609 eq9
    | (have j1 := eq2609 X0
       grind)
    | exact resolve eq9 eq2609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2609
  have eq2639 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (k (τ X0) (k (τ X0) (τ X0))) = (M.op (τ X0) (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq355 X0
       have i₂ := eq2612 (τ X0)
       grind)
    | exact superpose eq2612 eq355
    | (have j1 := eq2612 (τ X0)
       grind)
    | exact resolve eq355 eq2612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq2641 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op X0 X0)
       have i₂ := eq2612 X0
       grind)
    | exact superpose eq2612 eq9
    | (have j1 := eq2612 X0
       grind)
    | exact resolve eq9 eq2612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2612
  have eq2645 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (k (τ X0) (k (τ X0) (τ X0))) = (M.op (τ X0) (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2639 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2639
    | (have j0 := eq2639 X0
       grind)
    | exact resolve eq2639 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2639
  have eq2647 : ∀ X0 : G, (k (τ X0) (τ (k X0 X0))) = (M.op (τ X0) (τ (k X0 X0))) ∨ (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2645 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq2645
    | (have j0 := eq2645 X0
       grind)
    | exact resolve eq2645 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2645
  have eq2649 : ∀ X0 : G, (M.op (τ X0) (τ (k X0 X0))) = (τ (k X0 (k X0 X0))) ∨ (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2647 X0
       have i₂ := eq33 (k X0 X0) X0
       grind)
    | exact superpose eq33 eq2647
    | (have j0 := eq2647 X0
       grind)
    | exact resolve eq2647 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2647
  have eq3186 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq283 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq283
    | exact resolve eq283 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq3233 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3186 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3186
    | (have j0 := eq3186 X0 X1
       grind)
    | exact resolve eq3186 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3186
  have eq4284 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq282 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq282
    | exact resolve eq282 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq4368 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4284 X0 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq4284
    | (have j0 := eq4284 X0 X1
       grind)
    | exact resolve eq4284 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4284
  have eq7767 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1034
       have i₂ := eq3233 x y
       grind)
    | exact superpose eq3233 eq1034
    | (have j1 := eq3233 (σ x) (σ y)
       grind)
    | (have r₁ := eq1034
       have r₂ := eq3233 x y
       grind)
    | exact resolve eq1034 eq3233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034 eq3233
  have eq7768 : y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq7767
  have eq12674 : ∀ X0 : G, (τ (k (σ X0) (k (σ X0) (σ X0)))) = (M.op (τ (σ X0)) (k X0 (τ (σ X0)))) ∨ (σ X0) = (k (σ (M.op (τ (σ X0)) (τ (σ X0)))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2649 (σ X0)
       have i₂ := eq30 X0 (σ X0)
       grind)
    | exact superpose eq30 eq2649
    | (have j0 := eq2649 (σ X0)
       grind)
    | exact resolve eq2649 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2649
  have eq12687 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (τ (k (σ X0) (k (σ X0) (σ X0)))) ∨ (σ X0) = (k (σ (M.op (τ (σ X0)) (τ (σ X0)))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq12674 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12674
    | (have j0 := eq12674 X0
       grind)
    | exact resolve eq12674 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12674
  have eq12713 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (τ (σ X0)) (k X0 (τ (σ X0)))) ∨ (σ X0) = (k (σ (M.op (τ (σ X0)) (τ (σ X0)))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq12687 X0
       have i₂ := eq35 X0 (σ X0) (σ X0)
       grind)
    | exact superpose eq35 eq12687
    | (have j0 := eq12687 X0
       grind)
    | exact resolve eq12687 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq12687
  have eq12733 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (σ X0) = (k (σ (M.op (τ (σ X0)) (τ (σ X0)))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq12713 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12713
    | (have j0 := eq12713 X0
       grind)
    | exact resolve eq12713 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12713
  have eq12751 : ∀ X0 : G, (σ X0) = (σ (k (M.op (τ (σ X0)) (τ (σ X0))) X0)) ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12733 X0
       have i₂ := eq15 (M.op (τ (σ X0)) (τ (σ X0))) X0
       grind)
    | exact superpose eq15 eq12733
    | (have j0 := eq12733 X0
       grind)
    | exact resolve eq12733 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12733
  have eq12769 : ∀ X0 : G, (σ X0) = (σ (k (M.op X0 X0) X0)) ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12751 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12751
    | (have j0 := eq12751 X0
       grind)
    | exact resolve eq12751 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12751
  have eq12787 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op X0 X0) X0)) ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12769 X0
       have i₂ := eq348 X0
       grind)
    | exact superpose eq348 eq12769
    | (have j0 := eq12769 X0
       grind)
    | exact resolve eq12769 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12769
  have eq12824 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12787 X0
       have i₂ := eq2641 X0
       grind)
    | exact superpose eq2641 eq12787
    | (have j0 := eq12787 X0
       have j1 := eq2641 X0
       grind)
    | exact resolve eq12787 eq2641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2641
  have eq12878 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq12824 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12824
  have eq12926 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (k (M.op X0 X0) X1)) ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (M.op X0 X0) X1
       have i₂ := eq12878 X0
       grind)
    | exact superpose eq12878 eq15
    | (have j1 := eq12878 X0
       grind)
    | exact resolve eq15 eq12878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12878
  have eq13008 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (k (M.op X0 X0) X1)) ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12926 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq12926
    | (have j0 := eq12926 X0 X1
       grind)
    | exact resolve eq12926 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12926
  have eq13151 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (σ (k X0 X0)) ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13008 X0 X0
       have i₂ := eq348 X0
       grind)
    | exact superpose eq348 eq13008
    | (have j0 := eq13008 X0 x
       grind)
    | exact resolve eq13008 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13008
  have eq14039 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12787 X0
       have i₂ := eq13151 X0
       grind)
    | exact superpose eq13151 eq12787
    | (have j0 := eq12787 X0
       have j1 := eq13151 X0
       grind)
    | exact resolve eq12787 eq13151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12787 eq13151
  have eq14089 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq14039 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14039
  have eq14193 : ∀ X0 : G, (k X0 (σ (k (τ X0) (τ X0)))) = (σ (M.op (τ X0) (k (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq14089 (τ X0)
       grind)
    | exact superpose eq14089 eq19
    | (have j1 := eq14089 (τ X0)
       grind)
    | exact resolve eq19 eq14089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq14089
  have eq14244 : ∀ X0 : G, (k X0 (σ (τ (k X0 X0)))) = (σ (M.op (τ X0) (τ (k X0 X0)))) ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq14193 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq14193
    | (have j0 := eq14193 X0
       grind)
    | exact resolve eq14193 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14193
  have eq14302 : ∀ X0 : G, (k X0 (k X0 X0)) = (σ (M.op (τ X0) (τ (k X0 X0)))) ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq14244 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq14244
    | (have j0 := eq14244 X0
       grind)
    | exact resolve eq14244 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14244
  have eq14353 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) X0) ∨ (k X0 (k X0 X0)) = (σ (M.op (τ X0) (τ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq14302 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq14302
    | (have j0 := eq14302 X0
       grind)
    | exact resolve eq14302 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14302
  have eq14402 : ∀ X0 : G, (k X0 (k X0 X0)) = (σ (M.op (τ X0) (τ (k X0 X0)))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14353 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14353
    | (have j0 := eq14353 X0
       grind)
    | exact resolve eq14353 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14353
  have eq14583 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14402 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq14402
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq14402 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14402
  have eq14663 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq14583 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14583
  have eq14685 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    grind
  clear eq14663
  have eq15000 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ (k X0 X0))) = (σ (M.op (τ (σ X0)) (τ (σ (k X0 X0))))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq14685 (σ x)
       have i₂ := eq286 x x
       grind)
    | exact superpose eq286 eq14685
    | (have j0 := eq14685 (σ X0)
       have j1 := eq286 X0 X0
       grind)
    | exact resolve eq14685 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14685
  have eq15031 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ (k X0 X0))) = (σ (M.op (τ (σ X0)) (τ (σ (k X0 X0))))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq15000 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15000
  have eq15044 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (M.op (τ (σ X0)) (τ (σ (k X0 X0))))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq15031 X0
       have j1 := eq1043 X0
       grind)
    | (have r₁ := eq15031 X0
       have r₂ := eq1043 X0
       grind)
    | exact resolve eq15031 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15031
  have eq15055 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (M.op (τ (σ X0)) (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15044 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq15044
    | (have j0 := eq15044 X0
       grind)
    | exact resolve eq15044 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15044
  have eq15056 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (M.op X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15055 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15055
    | (have j0 := eq15055 X0
       grind)
    | exact resolve eq15055 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15055
  have eq25817 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 (k X0 X0))) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1037 X0 X0
       have i₂ := eq15056 X0
       grind)
    | exact superpose eq15056 eq1037
    | (have j0 := eq1037 X0 X0
       have j1 := eq15056 X0
       grind)
    | exact resolve eq1037 eq15056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037 eq15056
  have eq25822 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 (k X0 X0))) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq25817 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25817
  have eq53103 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (M.op (τ X0) (k (τ X0) (τ X0)))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25822 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25822
    | exact resolve eq25822 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53147 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (M.op (τ X0) (τ (k X0 X0)))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53103 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq53103
    | (have j0 := eq53103 X0
       grind)
    | exact resolve eq53103 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq53103
  have eq53230 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (M.op (τ X0) (τ (M.op X0 X0)))) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53147 X0
       have i₂ := eq4368 X0 X0
       grind)
    | exact superpose eq4368 eq53147
    | (have j0 := eq53147 X0
       have j1 := eq4368 X0 X0
       grind)
    | exact resolve eq53147 eq4368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4368 eq53147
  have eq53272 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (M.op (τ X0) (τ (M.op X0 X0)))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq53230 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53230
  have eq53380 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (M.op (τ (σ X0)) (τ (σ (k X0 X0))))) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq53272 (σ x)
       have i₂ := eq286 x x
       grind)
    | exact superpose eq286 eq53272
    | (have j0 := eq53272 (σ X0)
       have j1 := eq286 X0 X0
       grind)
    | exact resolve eq53272 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286 eq53272
  have eq53407 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (M.op (τ (σ X0)) (τ (σ (k X0 X0))))) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq53380 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53380
  have eq53420 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (M.op (τ (σ X0)) (τ (σ (k X0 X0))))) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq53407 X0
       have j1 := eq1043 X0
       grind)
    | (have r₁ := eq53407 X0
       have r₂ := eq1043 X0
       grind)
    | exact resolve eq53407 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043 eq53407
  have eq53426 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (M.op (τ (σ X0)) (k X0 X0))) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq53420 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq53420
    | (have j0 := eq53420 X0
       grind)
    | exact resolve eq53420 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53420
  have eq53430 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (M.op X0 (k X0 X0))) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq53426 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq53426
    | (have j0 := eq53426 X0
       grind)
    | exact resolve eq53426 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53426
  have eq53525 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq25822 X0
       have i₂ := eq53430 X0
       grind)
    | exact superpose eq53430 eq25822
    | (have j0 := eq25822 X0
       have j1 := eq53430 X0
       grind)
    | exact resolve eq25822 eq53430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25822 eq53430
  have eq53532 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq53525 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53525
  have eq53637 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq348 (σ X0)
       have i₂ := eq53532 X0
       grind)
    | exact superpose eq53532 eq348
    | (have j1 := eq53532 X0
       grind)
    | exact resolve eq348 eq53532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53532
  have eq53695 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq53637 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq53637
    | (have j0 := eq53637 X0
       grind)
    | exact resolve eq53637 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53637
  have eq53696 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq53695 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53695
  have eq53755 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq53696 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq53696
    | exact resolve eq53696 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53866 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ X0) (σ (k X0 X0))) := by
    intro X0
    grind
  have eq53868 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq348 (σ X0)
       have i₂ := eq53696 X0
       grind)
    | exact superpose eq53696 eq348
    | exact resolve eq348 eq53696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54064 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq53868 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq53868
    | exact resolve eq53868 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53868
  have eq54066 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq53866 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq53866
    | exact resolve eq53866 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53866
  have eq54147 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq53755 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq53755
    | exact resolve eq53755 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq53755
  have eq54299 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq54147 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq54147
    | exact resolve eq54147 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54147
  have eq55924 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq54064 X0
       have i₂ := eq54299 X0
       grind)
    | exact superpose eq54299 eq54064
    | exact resolve eq54064 eq54299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54064
  have eq56104 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq55924 X0
       have i₂ := eq348 X0
       grind)
    | exact superpose eq348 eq55924
    | exact resolve eq55924 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348 eq55924
  have eq56463 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq54066 X0
       have i₂ := eq54299 X0
       grind)
    | exact superpose eq54299 eq54066
    | exact resolve eq54066 eq54299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54066
  have eq56543 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq56463
  have eq568809 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq56543 x
       have i₂ := eq7768
       grind)
    | exact superpose eq7768 eq56543
    | exact resolve eq56543 eq7768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7768
  have eq568873 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq568809
       have r₂ := eq16
       grind)
    | exact resolve eq568809 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568809
  have eq569169 : (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq568873
       have i₂ := eq53696 y
       grind)
    | exact superpose eq53696 eq568873
    | exact resolve eq568873 eq53696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568873
  have eq569415 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq569169
       have i₂ := eq54299 y
       grind)
    | exact superpose eq54299 eq569169
    | exact resolve eq569169 eq54299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569169
  have eq569651 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq569415
       have i₂ := eq53696 x
       grind)
    | exact superpose eq53696 eq569415
    | exact resolve eq569415 eq53696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53696 eq569415
  have eq569850 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq569651
       have i₂ := eq54299 x
       grind)
    | exact superpose eq54299 eq569651
    | exact resolve eq569651 eq54299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54299 eq569651
  have eq570321 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq56104 y
       have i₂ := eq569850
       grind)
    | exact superpose eq569850 eq56104
    | exact resolve eq56104 eq569850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569850
  have eq570359 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq570321
       have r₂ := eq16
       grind)
    | exact resolve eq570321 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570321
  have eq570679 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq570359
       grind)
    | exact superpose eq570359 eq10
    | exact resolve eq10 eq570359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570359
  have eq571159 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq570679
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq570679
    | exact resolve eq570679 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570679
  have eq571868 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq56543 x
       have i₂ := eq571159
       grind)
    | exact superpose eq571159 eq56543
    | exact resolve eq56543 eq571159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56543 eq571159
  have eq571903 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq571868
       have r₂ := eq16
       grind)
    | exact resolve eq571868 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571868
  have eq572210 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq571903
       grind)
    | exact superpose eq571903 eq10
    | exact resolve eq10 eq571903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571903
  have eq572691 : x = (M.op y y) := by
    first
    | (have i₁ := eq572210
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq572210
    | exact resolve eq572210 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572210
  have eq573501 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56104 y
       have i₂ := eq572691
       grind)
    | exact superpose eq572691 eq56104
    | exact resolve eq56104 eq572691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56104 eq572691
  have eq573539 : False := by grind
  exact eq573539
