import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_x_pyy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X1)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq33
    | exact resolve eq33 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq9
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq22
  have eq65 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq66 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq86 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X1) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq37 (M.op (M.op (M.op X1 X2) X0) X1) X0 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq37
    | exact resolve eq37 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq37 X1 X2 X0
       grind)
    | exact superpose eq37 eq33
    | exact resolve eq33 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq65 x y
       grind)
    | exact superpose eq65 eq16
    | (have j1 := eq65 y y
       grind)
    | exact resolve eq16 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq65 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq65 X0 X1
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq65 X0 X1
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (M.op (M.op (σ (k X0 X1)) X2) (σ X1)) X2) = X2 ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X1) (σ X0)
       have i₂ := eq65 X1 X0
       grind)
    | exact superpose eq65 eq9
    | (have j1 := eq65 X0 X0
       grind)
    | exact resolve eq9 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq175 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq163 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq177 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq175 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq175 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq175 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq185 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq177 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 (τ X0) X1
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq185 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq185
    | (have j0 := eq185 X0 X1
       grind)
    | exact resolve eq185 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq190 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq187 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq187
    | (have j0 := eq187 X0 X1
       grind)
    | exact resolve eq187 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq196 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq190 (τ X0) X1
       have i₂ := eq44 X0 X0
       grind)
    | exact superpose eq44 eq190
    | (have j0 := eq190 (τ X0) X1
       grind)
    | exact resolve eq190 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq1205 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq161
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq161
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq161 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq1206 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq1205
  have eq1673 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (M.op (M.op (M.op (σ (k X0 X0)) X1) (σ X0)) X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq164 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq1674 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (M.op (M.op (σ (k X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1673 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673
  have eq4688 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op (σ (k (τ X0) (τ X0))) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1674 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1674
    | exact resolve eq1674 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674
  have eq4776 : ∀ X0 X1 : G, (M.op (M.op (M.op (k (σ (τ X0)) X0) X1) X0) X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4688 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq4688
    | (have j0 := eq4688 X0 X1
       grind)
    | exact resolve eq4688 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4688
  have eq4777 : ∀ X0 X1 : G, (M.op (M.op (M.op (k X0 X0) X1) X0) X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4776 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4776
    | (have j0 := eq4776 X0 X1
       grind)
    | exact resolve eq4776 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4776
  have eq4789 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op X0 X1) (k X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (k X0 X0) (k X0 X0) X1
       have i₂ := eq4777 X0 (k X0 X0)
       grind)
    | exact superpose eq4777 eq31
    | (have j1 := eq4777 X0 X1
       grind)
    | exact resolve eq31 eq4777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq4777
  have eq4973 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq66 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq4974 : ∀ X0 : G, (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4973 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4973
  have eq4978 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4974 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4974
    | (have j0 := eq4974 X0
       grind)
    | exact resolve eq4974 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4974
  have eq5084 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op X1 (M.op (M.op X0 X1) X0)) ∨ (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq93 X0 X0 X0
       have i₂ := eq4789 X0 X1
       grind)
    | exact superpose eq4789 eq93
    | (have j1 := eq4789 X0 X2
       grind)
    | exact resolve eq93 eq4789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4789
  have eq5158 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5084 X0 X1 X2
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq5084
    | (have j0 := eq5084 X0 X1 X2
       grind)
    | exact resolve eq5084 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5084
  have eq5568 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq5158 X0 (M.op (M.op X0 X0) (k X0 X0)) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5158
  have eq5569 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq5568 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5568
  have eq5879 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (k X0 X0) X0 X0
       have i₂ := eq5569 X0
       grind)
    | exact superpose eq5569 eq9
    | exact resolve eq9 eq5569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5881 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34 (k X0 X0) X0 X0
       have i₂ := eq5569 X0
       grind)
    | exact superpose eq5569 eq34
    | exact resolve eq34 eq5569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5882 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (k X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq86 (k X0 X0) X0 X0 X1
       have i₂ := eq5569 X0
       grind)
    | exact superpose eq5569 eq86
    | exact resolve eq86 eq5569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq5569
  have eq5957 : ∀ X0 : G, (τ X0) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq5881 (τ X0)
       have i₂ := eq44 X0 X0
       grind)
    | exact superpose eq44 eq5881
    | exact resolve eq5881 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq5963 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (k X0 X0)) = (M.op X1 (M.op (M.op X0 X1) (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (k X0 X0) X0
       have i₂ := eq5881 X0
       grind)
    | exact superpose eq5881 eq34
    | exact resolve eq34 eq5881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq5881
  have eq6308 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq5879 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq5879
    | exact resolve eq5879 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5879
  have eq6865 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (k X0 X0)) X1) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37 (τ (k X0 X0)) (τ X0) X1
       have i₂ := eq5957 X0
       grind)
    | exact superpose eq5957 eq37
    | exact resolve eq37 eq5957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq5957
  have eq7683 : ∀ X0 : G, (σ (σ (k X0 X0))) = (M.op (σ (σ X0)) (σ (σ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq6308 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq6308
    | exact resolve eq6308 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6308
  have eq10230 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq93 X0 y y
       have i₂ := eq1206
       grind)
    | exact superpose eq1206 eq93
    | exact resolve eq93 eq1206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206
  have eq10303 : ∀ X0 : G, x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq10230 x
       have i₂ := eq33 y x
       grind)
    | exact superpose eq33 eq10230
    | exact resolve eq10230 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10230
  have eq20763 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq4978 X0
       grind)
    | exact superpose eq4978 eq11
    | (have j1 := eq4978 X0
       grind)
    | exact resolve eq11 eq4978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4978
  have eq21414 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k X1 (σ X0)) = X1 ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq20763 X0
       grind)
    | exact superpose eq20763 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq20763 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq20763 X0
       grind)
    | exact resolve eq12 eq20763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21502 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq20763 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20763
  have eq21504 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq21414 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21414
  have eq21686 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21504 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21504
    | exact resolve eq21504 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21724 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ X0)) ∨ (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq196 (σ X0) X1
       have i₂ := eq21504 X0 (σ X0)
       grind)
    | exact superpose eq21504 eq196
    | (have j0 := eq196 (σ X0) X1
       have j1 := eq21504 X0 X1
       grind)
    | exact resolve eq196 eq21504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq21504
  have eq21836 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq21724 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21724
  have eq21896 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21836 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21836
    | (have j0 := eq21836 X0 X1
       grind)
    | exact resolve eq21836 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21836
  have eq21899 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21686 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq21686
    | (have j0 := eq21686 X0 X1
       grind)
    | exact resolve eq21686 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21686
  have eq21932 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21899 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21899
    | (have j0 := eq21899 X0 X1
       grind)
    | exact resolve eq21899 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21899
  have eq22300 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21896 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21896
    | (have j0 := eq21896 (τ X0) X1
       grind)
    | exact resolve eq21896 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21896
  have eq22490 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22300 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq22300
    | (have j0 := eq22300 X0 X1
       grind)
    | exact resolve eq22300 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq22300
  have eq22497 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22490 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22490
    | (have j0 := eq22490 X0 X1
       grind)
    | exact resolve eq22490 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22490
  have eq22585 : ∀ X0 : G, (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq7683 (τ X0)
       have i₂ := eq22497 X0 (τ X0)
       grind)
    | exact superpose eq22497 eq7683
    | (have j1 := eq22497 X0 x
       grind)
    | exact resolve eq7683 eq22497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7683 eq22497
  have eq22693 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq22585 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22585
    | (have j0 := eq22585 X0
       grind)
    | exact resolve eq22585 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22585
  have eq38687 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X1
       have i₂ := eq22693 X0
       grind)
    | exact superpose eq22693 eq177
    | (have j0 := eq177 X0 X1
       have j1 := eq22693 X0
       grind)
    | exact resolve eq177 eq22693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq22693
  have eq38906 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq38687 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq38687 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq38687 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38687
  have eq79347 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq21502 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq21502
    | exact resolve eq21502 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq21502
  have eq79387 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq79347 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq79347
    | (have j0 := eq79347 X0
       grind)
    | exact resolve eq79347 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79347
  have eq79409 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq79387 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq79387
    | (have j0 := eq79387 X0
       grind)
    | exact resolve eq79387 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79387
  have eq79424 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq79409 X0
       have j1 := eq21932 X0 x
       grind)
    | (have r₁ := eq79409 X0
       have r₂ := eq21932 X0 X0
       grind)
    | exact resolve eq79409 eq21932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21932 eq79409
  have eq80131 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq79424 (σ X0)
       grind)
    | exact superpose eq79424 eq15
    | exact resolve eq15 eq79424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80214 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq80131 X0
       have i₂ := eq79424 X0
       grind)
    | exact superpose eq79424 eq80131
    | exact resolve eq80131 eq79424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79424 eq80131
  have eq443403 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq38906 x X0
       have i₂ := eq10303 X1
       grind)
    | exact superpose eq10303 eq38906
    | (have j0 := eq38906 x X0
       have j1 := eq10303 X1
       grind)
    | exact resolve eq38906 eq10303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10303
  have eq443721 : ∀ X0 X1 : G, (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have j0 := eq443403 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443403
  have eq443910 : ∀ X0 X1 : G, (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have j0 := eq443721 X0 X1
       have j1 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq443721 X0 X1
       have r₂ := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq443721 X0 X1
       have r₂ := eq12 X0 (σ y)
       grind)
    | (have r₁ := eq443721 X0 y
       have r₂ := eq12 X0 y
       grind)
    | exact resolve eq443721 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443721
  have eq444068 : ∀ X0 X1 : G, (σ y) = (σ (M.op y y)) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq443910 X0 X1
       have i₂ := eq80214 y
       grind)
    | exact superpose eq80214 eq443910
    | (have j0 := eq443910 X0 X1
       grind)
    | exact resolve eq443910 eq80214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80214 eq443910
  have eq1311273 : ∀ X0 X1 : G, (M.op y y) = (τ (σ y)) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq444068 X0 X1
       grind)
    | exact superpose eq444068 eq10
    | (have j1 := eq444068 X0 X1
       grind)
    | exact resolve eq10 eq444068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444068
  have eq1312069 : ∀ X0 X1 : G, y = (M.op y y) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq1311273 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1311273
    | (have j0 := eq1311273 X0 y
       grind)
    | exact resolve eq1311273 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1311273
  have eq1312688 : ∀ X0 : G, y ≠ y ∨ (k X0 (σ x)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq1312069 X0 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312069
  have eq1312689 : ∀ X0 : G, y = (M.op y y) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq1312688 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312688
  have eq1319313 : ∀ X0 X1 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 y y
       have i₂ := eq1312689 X0
       grind)
    | exact superpose eq1312689 eq93
    | (have j1 := eq1312689 X1
       grind)
    | exact resolve eq93 eq1312689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq1312689
  have eq1319770 : ∀ X0 X1 : G, (k X1 (σ x)) = X1 ∨ y = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq1319313 X1 X1
       have i₂ := eq33 y X1
       grind)
    | exact superpose eq33 eq1319313
    | (have j0 := eq1319313 X0 X1
       grind)
    | exact resolve eq1319313 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319313
  have eq1325498 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq5882 (σ x) X0
       have i₂ := eq1319770 X1 (σ x)
       grind)
    | exact superpose eq1319770 eq5882
    | (have j1 := eq1319770 X1 X1
       grind)
    | exact resolve eq5882 eq1319770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5882
  have eq1325522 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (σ x)) X0) (τ (σ x))) X0) = X0 ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq6865 (σ x) X0
       have i₂ := eq1319770 X1 (σ x)
       grind)
    | exact superpose eq1319770 eq6865
    | (have j1 := eq1319770 X1 X1
       grind)
    | exact resolve eq6865 eq1319770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6865 eq1319770
  have eq1326314 : ∀ X0 X1 : G, (M.op (τ (σ x)) X0) = X0 ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq1325522 X0 X1
       have i₂ := eq33 (τ (σ x)) X0
       grind)
    | exact superpose eq33 eq1325522
    | (have j0 := eq1325522 X0 X1
       grind)
    | exact resolve eq1325522 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325522
  have eq1326338 : ∀ X0 X1 : G, (M.op (σ x) X0) = X0 ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq1325498 X0 X1
       have i₂ := eq33 (σ x) X0
       grind)
    | exact superpose eq33 eq1325498
    | (have j0 := eq1325498 X0 X1
       grind)
    | exact resolve eq1325498 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325498
  have eq1326688 : ∀ X0 X1 : G, (M.op x X0) = X0 ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq1326314 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1326314
    | (have j0 := eq1326314 X0 X1
       grind)
    | exact resolve eq1326314 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326314
  have eq1332278 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq1326688 y x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326688
  have eq1332279 : y = (M.op x y) := by grind
  clear eq1332278
  have eq1372693 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1326338 (σ y) X0
       grind)
    | exact superpose eq1326338 eq16
    | (have j1 := eq1326338 X0 X0
       grind)
    | exact resolve eq16 eq1326338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326338
  have eq1373355 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq1372693 X0
       have i₂ := eq1332279
       grind)
    | exact superpose eq1332279 eq1372693
    | (have j0 := eq1372693 X0
       grind)
    | exact resolve eq1372693 eq1332279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332279 eq1372693
  have eq1373356 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1373355 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1373355
  have eq1377024 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq38906 y X0
       have i₂ := eq1373356 y
       grind)
    | exact superpose eq1373356 eq38906
    | (have j0 := eq38906 y X0
       grind)
    | exact resolve eq38906 eq1373356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38906
  have eq1377991 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq1377024 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377024
  have eq1391159 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq5963 (σ y) x
       have i₂ := eq1377991 (σ y)
       grind)
    | exact superpose eq1377991 eq5963
    | exact resolve eq5963 eq1377991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5963 eq1377991
  have eq1391902 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1391159 x
       have i₂ := eq33 (σ y) x
       grind)
    | exact superpose eq33 eq1391159
    | exact resolve eq1391159 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq1391159
  have eq1419135 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1391902 (σ x)
       grind)
    | exact superpose eq1391902 eq16
    | exact resolve eq16 eq1391902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1391902
  have eq1419408 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1419135
       have i₂ := eq1373356 x
       grind)
    | exact superpose eq1373356 eq1419135
    | exact resolve eq1419135 eq1373356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1373356 eq1419135
  have eq1419409 : False := by grind
  exact eq1419409

/-- `Equation3263`: `x ◇ x = x ◇ (y ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_y_pxy_pxx_pxy_Equation3263 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3263 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3263.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq29 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq37 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq34 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq34 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq34 X1 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq43 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq22
    | (have j1 := eq14 X2 X0
       grind)
    | exact resolve eq22 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq54 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq43 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq43 X1 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq231 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq37 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq236 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq231 X0 X1
       have j1 := eq54 X1 X1 X0
       grind)
    | (have r₁ := eq231 X1 X0
       have r₂ := eq54 X0 X1 x
       grind)
    | (have r₁ := eq231 X0 X0
       have r₂ := eq54 X0 X0 x
       grind)
    | exact resolve eq231 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq231
  have eq239 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq236 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq236 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq236 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq275 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq239 (σ X0) (σ X1)
       grind)
    | exact superpose eq239 eq15
    | exact resolve eq15 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq275 X0 X1
       have i₂ := eq239 X0 X1
       grind)
    | exact superpose eq239 eq275
    | exact resolve eq275 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239 eq275
  have eq282 : False := by grind
  exact eq282

/-- `Equation3263`: `x ◇ x = x ◇ (y ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation3263 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3263 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3263.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq75 : y ≠ (M.op x y) ∨ y = (M.op y y) ∨ y = (k x y) := by
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
  have eq76 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq94 x y
       grind)
    | exact superpose eq94 eq44
    | (have j1 := eq94 x y
       grind)
    | exact resolve eq44 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq106
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq106
    | exact resolve eq106 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq117
    | exact resolve eq117 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq120 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq119
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119
    | exact resolve eq119 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq120 eq94
    | (have j0 := eq94 (σ x) (σ y)
       grind)
    | exact resolve eq94 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq123
    | exact resolve eq123 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq127 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq124
       have r₂ := eq27
       grind)
    | exact resolve eq124 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq129 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq127
    | exact resolve eq127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq131 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq129 eq27
    | exact resolve eq27 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq485 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq129 eq76
    | (have r₁ := eq76
       have r₂ := eq129
       grind)
    | exact resolve eq76 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq129
  have eq486 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq485
  have eq1287 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq486 eq120
    | exact resolve eq120 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq1291 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1287
  have eq1296 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1291
       have r₂ := eq131
       grind)
    | exact resolve eq1291 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq1291
  have eq1301 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1296 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq1296
       grind)
    | exact resolve eq13 eq1296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1296
  have eq1310 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1301 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1301
  have eq1319 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1310 eq120
    | exact resolve eq120 eq1310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq1310
  have eq1323 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1319
  have eq1328 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1323
    | exact resolve eq1323 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323
  have eq1330 : y = (M.op x y) := by
    first
    | (have r₁ := eq1328
       have r₂ := eq27
       grind)
    | exact resolve eq1328 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328
  have eq1332 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1330 eq20
    | exact resolve eq20 eq1330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1336 : y ≠ y ∨ y = (M.op y y) ∨ y = (k x y) := by
    first
    | exact superpose eq1330 eq75
    | (have r₁ := eq75
       have r₂ := eq1330
       grind)
    | exact resolve eq75 eq1330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq1330
  have eq1340 : y = (k x y) ∨ y = (M.op y y) := by grind
  clear eq1336
  have eq1347 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1332
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1332
    | exact resolve eq1332 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332
  have eq1349 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1347 eq26
    | exact resolve eq26 eq1347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2535 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1340
       grind)
    | exact superpose eq1340 eq44
    | exact resolve eq44 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340
  have eq2542 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1347 eq2535
    | exact resolve eq2535 eq1347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2535
  have eq2544 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2542
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2542
    | exact resolve eq2542 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2542
  have eq2545 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1347 eq2544
    | exact resolve eq2544 eq1347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2544
  have eq2548 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2545 eq94
    | (have j0 := eq94 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq94 eq2545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2545
  have eq2549 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by grind
  clear eq2548
  have eq2551 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1349 eq2549
    | exact resolve eq2549 eq1349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2549
  have eq2554 : y = (M.op y y) := by
    first
    | (have r₁ := eq2551
       have r₂ := eq27
       grind)
    | exact resolve eq2551 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2551
  have eq2559 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq2554
       grind)
    | exact superpose eq2554 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq2554
       grind)
    | exact resolve eq13 eq2554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2554
  have eq2571 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq2559 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2559
  have eq2586 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq2571 x
       grind)
    | exact superpose eq2571 eq44
    | exact resolve eq44 eq2571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq2571
  have eq2594 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1347 eq2586
    | exact resolve eq2586 eq1347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1347 eq2586
  have eq2598 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2594
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2594
    | exact resolve eq2594 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2594
  have eq2601 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq2598
    | exact resolve eq2598 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2598
  have eq2607 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2601 eq94
    | (have j0 := eq94 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq94 eq2601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq2601
  have eq2608 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq2607
  have eq2610 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1349 eq2608
    | exact resolve eq2608 eq1349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1349 eq2608
  have eq2613 : False := by grind
  exact eq2613

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pxy_pxx_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq27 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq14 (M.op X1 X0) (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq50
    | (have j0 := eq50 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq50 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq40 (τ X0)
       grind)
    | exact superpose eq40 eq19
    | exact resolve eq19 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq89 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq88 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq88
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq97 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq89 X0
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq89
    | exact resolve eq89 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq89
  have eq120 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X1
       have i₂ := eq27 X0 (τ X1)
       grind)
    | exact superpose eq27 eq97
    | exact resolve eq97 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq435 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq63 x y
       grind)
    | exact superpose eq63 eq16
    | (have j1 := eq63 x y
       grind)
    | exact resolve eq16 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq487 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq120 x X1
       have i₂ := eq27 x X0
       grind)
    | exact superpose eq27 eq120
    | exact resolve eq120 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq120
  have eq1379 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq435
       have i₂ := eq50 x y
       grind)
    | exact superpose eq50 eq435
    | (have j1 := eq50 (σ x) (σ y)
       grind)
    | (have r₁ := eq435
       have r₂ := eq50 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq435
       have r₂ := eq50 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq435 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq435
  have eq1380 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1379
  have eq1383 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1380
       grind)
    | exact superpose eq1380 eq16
    | exact resolve eq16 eq1380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1380
  have eq1384 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1383
       have r₂ := eq487 x (σ x)
       grind)
    | exact resolve eq1383 eq487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1383
  have eq1386 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1384
       grind)
    | exact superpose eq1384 eq10
    | exact resolve eq10 eq1384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384
  have eq1399 : x = y := by
    first
    | (have i₁ := eq1386
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1386
    | exact resolve eq1386 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1386
  have eq1401 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1399
       grind)
    | exact superpose eq1399 eq16
    | exact resolve eq16 eq1399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399
  have eq1402 : False := by grind
  exact eq1402

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyy_pxy_pxx_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq19 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op X3 (M.op X1 (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X1 X3 X4
       have i₂ := eq9 X1 X0 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X1 (M.op X3 (M.op X0 (M.op X1 (M.op X0 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X1 X1
       have i₂ := eq9 X1 X0 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 (M.op X0 (M.op X2 x))
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X3))) = (M.op X1 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X2) X1 X2
       have i₂ := eq9 (M.op X1 X2) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ X1 ∨ (M.op X0 (M.op X1 (M.op X0 X2))) = (k X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 (M.op (M.op X1 X2) (M.op X1 X2)) X1
       have r₂ := eq9 (M.op X1 X2) X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ (M.op X0 (M.op X1 (M.op X0 X2))) ∨ (M.op X0 (M.op X1 (M.op X0 X2))) = X1 ∨ (M.op X0 (M.op X1 (M.op X0 X2))) = (k X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = X1 ∨ (M.op X0 (M.op X1 (M.op X0 X2))) = (k X1 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq26 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq28 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq28 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq28 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq31 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (k X1 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq29 X0 X1 X2
       have j1 := eq24 X0 X1 X2
       grind)
    | (have r₁ := eq29 X0 X1 X2
       have r₂ := eq24 X0 X1 X2
       grind)
    | exact resolve eq29 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq29
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op X1 (M.op X2 X3))) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 X3
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq43 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq46 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq46 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op X1 (M.op X2 X3))) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq41 X0 X1 X2 X3
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq41 (M.op X1 X3) (M.op X1 X3) X1 X3
       have r₂ := eq12 (M.op (M.op X1 X3) (M.op X1 X3)) X1
       grind)
    | (have r₁ := eq41 X0 X1 X2 X3
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq57 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq48 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq48 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq60 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq61 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       have j1 := eq60 X0 X1
       grind)
    | (have r₁ := eq61 X0 X1
       have r₂ := eq60 X0 X1
       grind)
    | exact resolve eq61 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq61
  have eq66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq30 (σ X0)
       grind)
    | exact superpose eq30 eq15
    | exact resolve eq15 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq66
    | exact resolve eq66 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq81 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 X2
       have i₂ := eq22 X0 X2
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq88 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81 X0 X1 X2
       have i₂ := eq21 X0 X0 X1
       grind)
    | exact superpose eq21 eq81
    | exact resolve eq81 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq81
  have eq106 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq171 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ X1) (M.op X0 X2))) = (σ (k X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X1
       have i₂ := eq31 X0 (σ X1) X2
       grind)
    | exact superpose eq31 eq15
    | exact resolve eq15 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ X1) (M.op X0 X2))) = (σ (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq171 X0 X1 X2
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq171
    | exact resolve eq171 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq171
  have eq196 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq57
    | exact resolve eq57 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq57 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq228 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq196 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq196
    | (have j0 := eq196 X0 X1
       grind)
    | exact resolve eq196 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq196
  have eq375 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X3 (M.op X0 (M.op X1 (M.op X0 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 X1 X3 x X3
       have i₂ := eq19 X3 X1 (M.op X1 x) X0 X2
       grind)
    | (have i₁ := eq20 X1 X3 x X3
       have i₂ := eq19 X0 X1 X2 X3 (M.op X1 x)
       grind)
    | exact superpose eq19 eq20
    | exact resolve eq20 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20
  have eq618 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op (σ y) (M.op X0 X1))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq53 (σ x) (σ y) X0 X1
       grind)
    | exact superpose eq53 eq16
    | (have j1 := eq53 (σ x) (σ y) x x
       grind)
    | exact resolve eq16 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq667 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op (σ y) (M.op X0 X1))) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq618 X0 X1
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq618
    | (have j0 := eq618 X0 X1
       grind)
    | exact resolve eq618 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq752 : ∀ X0 X1 X2 X3 : G, (k X1 X1) = (M.op X0 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq31 X0 X1 (M.op (M.op X1 X2) (M.op X0 X3))
       have i₂ := eq23 X0 X1 X2 X3
       grind)
    | exact superpose eq23 eq31
    | exact resolve eq31 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq31
  have eq763 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq752 X0 X1 x x
       have i₂ := eq375 X0 (M.op X1 x) x X0
       grind)
    | exact superpose eq375 eq752
    | exact resolve eq752 eq375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375 eq752
  have eq1442 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k X0 X0) ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X1 X2
       have i₂ := eq763 X2 X0
       grind)
    | exact superpose eq763 eq64
    | (have j0 := eq64 X1 X2
       grind)
    | exact resolve eq64 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq2140 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    intro X0
    first
    | (have i₁ := eq667 (σ X0) (M.op (σ y) x)
       have i₂ := eq177 (σ y) X0 x
       grind)
    | exact superpose eq177 eq667
    | exact resolve eq667 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq667
  have eq2177 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (k X0 X0) ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq215 X1 X2
       have i₂ := eq763 X1 X0
       grind)
    | exact superpose eq763 eq215
    | (have j0 := eq215 X1 X2
       grind)
    | exact resolve eq215 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq763
  have eq2225 : ∀ X1 X2 : G, (M.op X1 X2) = (k X1 X2) := by
    intro X1 X2
    first
    | (have j0 := eq2177 x X1 X2
       have j1 := eq1442 x X1 X2
       grind)
    | (have r₁ := eq2177 x X1 X2
       have r₂ := eq1442 x X1 X2
       grind)
    | (have r₁ := eq2177 X2 X2 X2
       have r₂ := eq1442 x X2 X2
       grind)
    | exact resolve eq2177 eq1442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1442 eq2177
  have eq2269 : ∀ X0 X1 X2 : G, (k (σ X1) (k (σ X0) (σ X2))) = (σ (k X1 (k X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq106 (σ X0) X2 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq106
    | exact resolve eq106 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq2304 : ∀ X0 X1 X2 : G, (k (σ X1) (k (σ X0) (σ X2))) = (σ (M.op X1 (k X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2269 X0 X1 X2
       have i₂ := eq2225 X1 (k X0 X2)
       grind)
    | exact superpose eq2225 eq2269
    | exact resolve eq2269 eq2225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269
  have eq2320 : ∀ X0 X1 X2 : G, (k (σ X1) (k (σ X0) (σ X2))) = (σ (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2304 X0 X1 X2
       have i₂ := eq2225 X0 X2
       grind)
    | exact superpose eq2225 eq2304
    | exact resolve eq2304 eq2225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2304
  have eq2336 : ∀ X0 X1 X2 : G, (σ (M.op X1 (M.op X0 X2))) = (M.op (σ X1) (k (σ X0) (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2320 X0 X1 X2
       have i₂ := eq2225 (σ X1) (k (σ X0) (σ X2))
       grind)
    | exact superpose eq2225 eq2320
    | exact resolve eq2320 eq2225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2320
  have eq2350 : ∀ X0 X1 X2 : G, (σ (M.op X1 (M.op X0 X2))) = (M.op (σ X1) (σ (k X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2336 X0 X1 X2
       have i₂ := eq15 X0 X2
       grind)
    | exact superpose eq15 eq2336
    | exact resolve eq2336 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2336
  have eq2361 : ∀ X0 X1 X2 : G, (σ (M.op X1 (M.op X0 X2))) = (M.op (σ X1) (σ (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2350 X0 X1 X2
       have i₂ := eq2225 X0 X2
       grind)
    | exact superpose eq2225 eq2350
    | exact resolve eq2350 eq2225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2350
  have eq3784 : ∀ X0 X1 X2 X3 : G, (σ (k X2 X3)) = (σ (M.op X0 (M.op X1 X1))) ∨ (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq228 X2 X3
       have i₂ := eq88 X1 X2 X0
       grind)
    | (have i₁ := eq228 (M.op X0 X0) X1
       have i₂ := eq88 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq88 eq228
    | (have j0 := eq228 X2 X3
       grind)
    | exact resolve eq228 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq3893 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 (M.op X1 X1))) = (σ (M.op X2 X3)) ∨ (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3784 X0 X1 X2 X3
       have i₂ := eq2225 X2 X3
       grind)
    | exact superpose eq2225 eq3784
    | (have j0 := eq3784 X0 X1 X2 X3
       grind)
    | exact resolve eq3784 eq2225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3784
  have eq3940 : ∀ X0 X1 X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (M.op X2 X3)) ∨ (σ (M.op X0 (M.op X1 X1))) = (σ (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3893 X0 X1 X2 X3
       have i₂ := eq2225 X2 X3
       grind)
    | exact superpose eq2225 eq3893
    | (have j0 := eq3893 X0 X1 X2 X3
       grind)
    | exact resolve eq3893 eq2225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3893
  have eq42541 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op (σ (M.op X1 X1)) (σ (M.op X0 X0))) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq2140 (M.op X1 X1)
       have i₂ := eq88 X1 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq2140 X1
       have i₂ := eq88 X0 X1 x
       grind)
    | exact superpose eq88 eq2140
    | exact resolve eq2140 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq2140
  have eq42594 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (M.op (M.op X1 X1) (M.op X0 X0))) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq42541 X0 X1
       have i₂ := eq2361 X0 (M.op X1 X1) X0
       grind)
    | exact superpose eq2361 eq42541
    | exact resolve eq42541 eq2361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2361 eq42541
  have eq42659 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (M.op (M.op X1 X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq42594 X0 X1
       have i₂ := eq2225 x y
       grind)
    | exact superpose eq2225 eq42594
    | (have j0 := eq42594 X0 X1
       grind)
    | exact resolve eq42594 eq2225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2225 eq42594
  have eq42719 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq3940 x x x y
       grind)
    | (have r₁ := eq42659 x x
       have r₂ := eq3940 (M.op x x) x x y
       grind)
    | exact resolve eq42659 eq3940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3940 eq42659
  have eq42774 : False := by grind
  exact eq42774

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_y_pxy_pyy_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
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
  have eq29 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq79 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq44
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq44 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq103
    | exact resolve eq103 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq111
    | exact resolve eq111 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq232 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x X0
       have i₂ := eq55 x X1
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1781 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq112 eq79
    | (have j0 := eq79 x (σ y)
       grind)
    | exact resolve eq79 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq1782 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq1781
    | exact resolve eq1781 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1781
  have eq1785 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1782
       have r₂ := eq27
       grind)
    | exact resolve eq1782 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1782
  have eq1796 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1785 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq1785
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq1785
       grind)
    | exact resolve eq13 eq1785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1785
  have eq1806 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq1796
  have eq1838 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1806 eq89
    | exact resolve eq89 eq1806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq1806
  have eq1842 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq1838
    | exact resolve eq1838 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1838
  have eq2395 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq79 y y
       have i₂ := eq1842
       grind)
    | exact superpose eq1842 eq79
    | (have j0 := eq79 x y
       grind)
    | exact resolve eq79 eq1842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1842
  have eq2396 : y = (M.op y y) := by grind
  clear eq2395
  have eq2606 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq2396
       have i₂ := eq232 y X0
       grind)
    | (have i₁ := eq2396
       have i₂ := eq232 X0 y
       grind)
    | exact superpose eq232 eq2396
    | exact resolve eq2396 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq2620 : y ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq2396
       grind)
    | exact superpose eq2396 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq2396
       grind)
    | exact resolve eq13 eq2396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2396
  have eq2631 : y = (k y y) := by grind
  clear eq2620
  have eq2694 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op x x) x x
       have i₂ := eq2606 (M.op x x)
       grind)
    | exact superpose eq2606 eq14
    | exact resolve eq14 eq2606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2712 : y = (M.op x y) := by
    first
    | (have i₁ := eq51 sF0
       have i₂ := eq2606 sF0
       grind)
    | exact superpose eq2606 eq51
    | exact resolve eq51 eq2606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq2726 : y = (M.op x y) := by
    first
    | (have i₁ := eq2712
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2712
    | exact resolve eq2712 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2712
  have eq2758 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq2726 eq20
    | exact resolve eq20 eq2726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2726
  have eq2781 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2758
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2758
    | exact resolve eq2758 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2758
  have eq2782 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2781 eq26
    | exact resolve eq26 eq2781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2808 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq2631
       grind)
    | exact superpose eq2631 eq77
    | exact resolve eq77 eq2631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq2631
  have eq2812 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2781 eq2808
    | exact resolve eq2808 eq2781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2808
  have eq2813 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2812
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2812
    | exact resolve eq2812 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2812
  have eq2814 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2781 eq2813
    | exact resolve eq2813 eq2781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2781 eq2813
  have eq2878 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2814 eq79
    | (have j0 := eq79 x (σ (M.op x y))
       grind)
    | exact resolve eq79 eq2814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq2814
  have eq2879 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq2878
  have eq2881 : y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq2879
       have i₂ := eq2606 sF1
       grind)
    | exact superpose eq2606 eq2879
    | exact resolve eq2879 eq2606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2606 eq2879
  have eq2987 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq2881 eq2782
    | exact resolve eq2782 eq2881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2782
  have eq2988 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2987
       have i₂ := eq2694 sF2
       grind)
    | exact superpose eq2694 eq2987
    | exact resolve eq2987 eq2694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2694 eq2987
  have eq2990 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq2988 eq27
    | exact resolve eq27 eq2988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2988
  have eq3001 : False := by grind
  exact eq3001

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_x_pxy_pxx_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : (M.op x y) = (M.op x y) := by grind
  have eq19 : (M.op x y) = (M.op x y) := by grind
  clear eq18
  have eq20 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq20
  have eq22 : (σ x) = (σ x) := by grind
  have eq23 : (σ x) = (σ x) := by grind
  clear eq22
  have eq24 : (σ y) = (σ y) := by grind
  have eq25 : (σ y) = (σ y) := by grind
  clear eq24
  have eq26 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq26
  have eq28 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq29 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X1 (M.op X3 (M.op X0 (M.op X1 (M.op X0 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X1 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X1 (M.op X0 X2))) X1) = (M.op (M.op X0 (M.op X1 (M.op X0 X2))) X1) := by
    intro X0 X1 X2
    grind
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq84
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq84
    | exact resolve eq84 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq92
    | exact resolve eq92 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq233 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56 x X0
       have i₂ := eq56 x X1
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 X1
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq296 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq951 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X0)) X1) = (M.op (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq67 x X1 (M.op X0 (M.op X1 (M.op X0 x)))
       have i₂ := eq54 X0 X1 x x
       grind)
    | exact superpose eq54 eq67
    | exact resolve eq67 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq67
  have eq977 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq951 X0 X1
       have i₂ := eq241 X0 X0
       grind)
    | exact superpose eq241 eq951
    | exact resolve eq951 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq1383 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X0
       have i₂ := eq56 X0 (σ X0)
       grind)
    | exact superpose eq56 eq77
    | exact resolve eq77 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1399 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X1 (σ X0)
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq56
    | (have j1 := eq77 X0 X0
       grind)
    | exact resolve eq56 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1417 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq77 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1418 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1417 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417
  have eq1428 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1399 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399
  have eq1444 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1383 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1383
  have eq1450 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1428 X0 X1
       have i₂ := eq241 X1 X1
       grind)
    | exact superpose eq241 eq1428
    | (have j0 := eq1428 X0 X1
       grind)
    | exact resolve eq1428 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428
  have eq1452 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1444 X0 X1
       have i₂ := eq241 X0 X0
       grind)
    | exact superpose eq241 eq1444
    | (have j0 := eq1444 X0 X1
       grind)
    | exact resolve eq1444 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1444
  have eq1481 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1452 X0 X1
       have i₂ := eq241 X0 X0
       grind)
    | exact superpose eq241 eq1452
    | (have j0 := eq1452 X0 X1
       grind)
    | exact resolve eq1452 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq1452
  have eq1482 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq296 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq296
    | exact resolve eq296 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq5643 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X1)
       have i₂ := eq1481 X0 (τ X1)
       grind)
    | exact superpose eq1481 eq35
    | (have j1 := eq1481 X0 (τ X1)
       grind)
    | exact resolve eq35 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1481
  have eq5673 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5643 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq5643
    | (have j0 := eq5643 X0 X1
       grind)
    | exact resolve eq5643 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5643
  have eq5733 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5673 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq5673
    | (have j0 := eq5673 X0 X1
       grind)
    | exact resolve eq5673 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5673
  have eq8376 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5733 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5733
  have eq8487 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8376 X1 (τ X0)
       have i₂ := eq1482 X0 X0
       grind)
    | exact superpose eq1482 eq8376
    | (have j0 := eq8376 X1 (τ X0)
       grind)
    | exact resolve eq8376 eq1482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1482
  have eq10356 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1418 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq1418
    | (have j0 := eq1418 (τ X0)
       grind)
    | exact resolve eq1418 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10364 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq10356 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10356
    | (have j0 := eq10356 X0
       grind)
    | exact resolve eq10356 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10356
  have eq10373 : ∀ X0 : G, (σ (τ X0)) = (M.op x (M.op (σ (τ X0)) (M.op x y))) ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq10364 X0
       have i₂ := eq52 (σ (τ X0))
       grind)
    | exact superpose eq52 eq10364
    | (have j0 := eq10364 X0
       grind)
    | exact resolve eq10364 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10364
  have eq10378 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op x (M.op X0 (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq10373 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10373
    | (have j0 := eq10373 X0
       grind)
    | exact resolve eq10373 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10373
  have eq10510 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (σ (k (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1450 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1450
    | (have j0 := eq1450 (τ X0) X1
       grind)
    | exact resolve eq1450 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10591 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ (k x x)) := by
    intro X0
    first
    | (have i₁ := eq1450 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1450
    | (have j0 := eq1450 x X0
       grind)
    | exact resolve eq1450 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1450
  have eq10697 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10591 X0
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq10591
    | exact resolve eq10591 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10591
  have eq10777 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 (σ (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10510 X0 X1
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq10510
    | (have j0 := eq10510 X0 X1
       grind)
    | exact resolve eq10510 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq10510
  have eq10780 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10777 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10777
    | (have j0 := eq10777 X0 X1
       grind)
    | exact resolve eq10777 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10777
  have eq11393 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (σ x) = (M.op x (M.op (σ x) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq10697 eq10378
    | (have j0 := eq10378 (σ x)
       grind)
    | exact resolve eq10378 eq10697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10378 eq10697
  have eq11404 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq52 eq11393
    | (have j0 := eq11393 X0
       grind)
    | exact resolve eq11393 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq11393
  have eq11405 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq11404 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11404
  have eq11671 : ∀ X0 : G, (k (σ x) (σ x)) = (σ (M.op X0 X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq44
       have i₂ := eq10780 x X0
       grind)
    | exact superpose eq10780 eq44
    | (have j1 := eq10780 x x
       grind)
    | exact resolve eq44 eq10780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq10780
  have eq18599 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq78 X0
       grind)
    | (have r₁ := eq78 X0
       have r₂ := eq11405 (σ x)
       grind)
    | (have r₁ := eq78 X0
       have r₂ := eq11405 (σ X0)
       grind)
    | exact resolve eq78 eq11405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq18969 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq18599 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18599
    | (have j0 := eq18599 y
       grind)
    | exact resolve eq18599 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq18599
  have eq18988 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq18969
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq18969
    | exact resolve eq18969 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18969
  have eq19008 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq18988
    | exact resolve eq18988 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18988
  have eq44095 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq93 eq19008
    | exact resolve eq19008 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq19008
  have eq44106 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq44095
       have r₂ := eq28
       grind)
    | exact resolve eq44095 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44095
  have eq44125 : ∀ X0 : G, x = (M.op y y) ∨ x = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq44106
       have i₂ := eq233 sF2 x
       grind)
    | (have i₁ := eq44106
       have i₂ := eq233 X0 sF2
       grind)
    | exact superpose eq233 eq44106
    | exact resolve eq44106 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44106
  have eq44249 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq11671 y
       have i₂ := eq44125 X0
       grind)
    | exact superpose eq44125 eq11671
    | (have j1 := eq44125 X0
       grind)
    | exact resolve eq11671 eq44125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11671 eq44125
  have eq44274 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq44249 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44249
  have eq44287 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq44274 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq44274
    | (have j0 := eq44274 X0
       grind)
    | exact resolve eq44274 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44274
  have eq44298 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq44287 X0
       have j1 := eq8376 x x
       grind)
    | (have r₁ := eq44287 X0
       have r₂ := eq8376 X0 (σ x)
       grind)
    | exact resolve eq44287 eq8376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8376 eq44287
  have eq44302 : ∀ X0 : G, (k x x) = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    grind
  have eq45328 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq1418 x
       have i₂ := eq44302 X0
       grind)
    | exact superpose eq44302 eq1418
    | (have j0 := eq1418 x
       have j1 := eq44302 (σ x)
       grind)
    | exact resolve eq1418 eq44302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1418 eq44302
  have eq45367 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq45328 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq45328
    | (have j0 := eq45328 (σ x)
       grind)
    | exact resolve eq45328 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45328
  have eq45385 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (σ (M.op x x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq45367 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq45367
    | (have j0 := eq45367 (σ x)
       grind)
    | exact resolve eq45367 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45367
  have eq45394 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j0 := eq45385 (σ x)
       grind)
    | (have r₁ := eq45385 x
       have r₂ := eq11405 (σ x)
       grind)
    | (have r₁ := eq45385 x
       have r₂ := eq11405 x
       grind)
    | exact resolve eq45385 eq11405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45385
  have eq45985 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq45394
       have i₂ := eq44298 X0
       grind)
    | exact superpose eq44298 eq45394
    | (have j1 := eq44298 (σ x)
       grind)
    | exact resolve eq45394 eq44298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44298 eq45394
  have eq46002 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j0 := eq45985 (σ x)
       grind)
    | (have r₁ := eq45985 x
       have r₂ := eq11405 (σ x)
       grind)
    | (have r₁ := eq45985 x
       have r₂ := eq11405 x
       grind)
    | exact resolve eq45985 eq11405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11405 eq45985
  have eq46004 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq46002
       have r₂ := eq23
       grind)
    | exact resolve eq46002 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq46002
  have eq46005 : ∀ X0 : G, (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq46004
       have i₂ := eq233 sF2 x
       grind)
    | (have i₁ := eq46004
       have i₂ := eq233 X0 sF2
       grind)
    | exact superpose eq233 eq46004
    | exact resolve eq46004 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq46008 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by grind
  have eq46025 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq46004 eq977
    | exact resolve eq977 eq46004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq46082 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq46004 eq46008
    | exact resolve eq46008 eq46004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46004 eq46008
  have eq46592 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (M.op X0 X0) = (τ (σ x)) := by
    intro X0
    first
    | exact superpose eq46082 eq8487
    | (have j0 := eq8487 (σ x) X0
       grind)
    | exact resolve eq8487 eq46082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8487 eq46082
  have eq46611 : ∀ X0 : G, (M.op X0 X0) = (τ (σ x)) := by
    intro X0
    first
    | (have j0 := eq46592 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46592
  have eq46631 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq29 eq46611
    | exact resolve eq46611 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq46611
  have eq46651 : x = (σ x) := by
    first
    | (have i₁ := eq46631 x
       have i₂ := eq46005 x
       grind)
    | exact superpose eq46005 eq46631
    | exact resolve eq46631 eq46005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46005 eq46631
  have eq46655 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq46651 eq27
    | exact resolve eq27 eq46651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq49275 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq46651 eq46025
    | exact resolve eq46025 eq46651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46025
  have eq49351 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq49275 y
       grind)
    | exact superpose eq49275 eq45
    | exact resolve eq45 eq49275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq49387 : (σ (M.op x y)) = (k x (σ y)) := by
    first
    | exact superpose eq46651 eq49351
    | exact resolve eq49351 eq46651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46651 eq49351
  have eq49464 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq49387
       have i₂ := eq49275 sF3
       grind)
    | exact superpose eq49275 eq49387
    | exact resolve eq49387 eq49275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49275 eq49387
  have eq49536 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46655 eq49464
    | exact resolve eq49464 eq46655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46655 eq49464
  have eq49584 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq49536
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq49536
    | exact resolve eq49536 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq49536
  have eq49617 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq49584
    | exact resolve eq49584 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq49584
  have eq49637 : False := by grind
  exact eq49637

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_pyy_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq52 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op X3 (M.op X1 (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X1 X3 X4
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq28 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X1 (M.op X3 (M.op X0 (M.op X1 (M.op X0 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X1 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op X0 (M.op X2 x))
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X3))) = (M.op X1 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X2) X1 X2
       have i₂ := eq14 (M.op X1 X2) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X1 (M.op X0 X2))) X1) = (M.op (M.op X0 (M.op X1 (M.op X0 X2))) X1) := by
    intro X0 X1 X2
    grind
  have eq78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq46
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq85
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq85
    | exact resolve eq85 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq93
    | exact resolve eq93 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq119 : ∀ X0 X1 X2 : G, (k X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X0 X0) (M.op X1 X2))) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq215 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op x (M.op X1 (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X1 (M.op x (M.op X0 (M.op x y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 X0
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 x X0
       have i₂ := eq57 x X1
       grind)
    | exact superpose eq57 eq57
    | exact resolve eq57 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 X1
       have i₂ := eq57 X1 X0
       grind)
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq331 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq16
    | exact resolve eq16 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 X1 X2 : G, (M.op x (M.op X0 (M.op x y))) = (M.op X1 (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X2 X0 X1
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq439 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X1 X1 X2
       have i₂ := eq57 X1 X0
       grind)
    | exact superpose eq57 eq56
    | exact resolve eq56 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq551 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X2)))) = (M.op X3 (M.op X4 (M.op X3 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 X3 X4 X5 X1 (M.op X4 x)
       have i₂ := eq52 X4 X1 x X0 X2
       grind)
    | (have i₁ := eq52 X3 X4 X5 X1 (M.op X4 x)
       have i₂ := eq52 X0 X1 X2 X4 x
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : ∀ X0 X3 X4 X5 : G, (M.op X0 X0) = (M.op X3 (M.op X4 (M.op X3 X5))) := by
    intro X0 X3 X4 X5
    first
    | (have i₁ := eq551 X0 x x X3 X4 X5
       have i₂ := eq14 X0 x (M.op X0 x)
       grind)
    | exact superpose eq14 eq551
    | exact resolve eq551 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq667 : ∀ X0 X1 X2 : G, (M.op x (M.op X0 (M.op x y))) = (M.op X1 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq439 X2 X0 X1
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq439
    | exact resolve eq439 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq725 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X1 X1))) = (M.op X2 (M.op (M.op X3 X4) (M.op X2 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 X2 (M.op X3 X4) X5 X3 X4
       have i₂ := eq439 X1 (M.op X3 X4) X0
       grind)
    | (have i₁ := eq52 X0 X2 X2 X0 X0
       have i₂ := eq439 X0 X1 X2
       grind)
    | exact superpose eq439 eq52
    | exact resolve eq52 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1094 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X0)) X1) = (M.op (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq68 x X1 (M.op X0 (M.op X1 (M.op X0 x)))
       have i₂ := eq55 X0 X1 x x
       grind)
    | exact superpose eq55 eq68
    | exact resolve eq68 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1097 : ∀ X0 X1 : G, (k (M.op X1 (M.op X0 X0)) X1) = (M.op (M.op X1 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 X0 X0
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq68
    | exact resolve eq68 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1127 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1094 X0 X1
       have i₂ := eq262 X0 X0
       grind)
    | exact superpose eq262 eq1094
    | exact resolve eq1094 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094
  have eq1224 : ∀ X0 X1 X2 X3 : G, (k (M.op X0 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X3)))) X1) = (M.op (M.op X0 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X3)))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq68 X0 X1 (M.op (M.op X1 X2) (M.op X0 X3))
       have i₂ := eq58 X0 X1 X2 X3
       grind)
    | exact superpose eq58 eq68
    | exact resolve eq68 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq68
  have eq1317 : ∀ X0 X1 X2 : G, (k X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X0 X0) (M.op X1 X2))) ∨ (M.op x (M.op (M.op X0 X0) (M.op x y))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq119 X0 X1 X2
       have i₂ := eq53 (M.op X0 X0)
       grind)
    | exact superpose eq53 eq119
    | (have j0 := eq119 X0 X1 X2
       grind)
    | exact resolve eq119 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq1381 : ∀ X0 X1 : G, (k X1 (M.op X1 X1)) = (M.op X1 (M.op X0 (M.op X0 X0))) ∨ (M.op x (M.op (M.op X1 X1) (M.op x y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1317 X1 X1 X1
       have i₂ := eq57 X0 (M.op X1 X1)
       grind)
    | exact superpose eq57 eq1317
    | (have j0 := eq1317 X1 X1 x
       grind)
    | exact resolve eq1317 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1317
  have eq1432 : ∀ X0 X1 : G, (M.op x (M.op (M.op X1 X1) (M.op x y))) = X1 ∨ (M.op X0 X0) = (k X1 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1381 X0 X1
       have i₂ := eq56 X0 X0 X1
       grind)
    | exact superpose eq56 eq1381
    | (have j0 := eq1381 X0 X1
       grind)
    | exact resolve eq1381 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381
  have eq1571 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq331 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq331
    | exact resolve eq331 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq1685 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 X0
       have i₂ := eq57 X0 (σ X0)
       grind)
    | exact superpose eq57 eq78
    | exact resolve eq78 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq1758 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1685 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1685
  have eq1771 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1758 X0 X1
       have i₂ := eq262 X0 X0
       grind)
    | exact superpose eq262 eq1758
    | (have j0 := eq1758 X0 X1
       grind)
    | exact resolve eq1758 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1758
  have eq1801 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1771 X0 X1
       have i₂ := eq262 X0 X0
       grind)
    | exact superpose eq262 eq1771
    | (have j0 := eq1771 X0 X1
       grind)
    | exact resolve eq1771 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1771
  have eq3093 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op X3 (M.op X0 (M.op X1 (M.op X0 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq220 X0 (M.op x (M.op X0 sF0))
       have i₂ := eq585 (M.op x (M.op X0 sF0)) X3 x x
       grind)
    | exact superpose eq585 eq220
    | exact resolve eq220 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq585
  have eq3236 : ∀ X1 X3 : G, (M.op x (M.op X1 (M.op x y))) = (M.op X3 (M.op x (M.op X1 (M.op x y)))) := by
    intro X1 X3
    first
    | (have i₁ := eq3093 x X1 x X3
       have i₂ := eq215 x X1 x
       grind)
    | (have i₁ := eq3093 x X1 y X3
       have i₂ := eq215 x X1 x
       grind)
    | exact superpose eq215 eq3093
    | (have j0 := eq3093 x X1 y X3
       grind)
    | exact resolve eq3093 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3093
  have eq7550 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X1 (τ X1)
       have i₂ := eq1801 X0 (τ X1)
       grind)
    | exact superpose eq1801 eq36
    | (have j1 := eq1801 X0 (τ X1)
       grind)
    | exact resolve eq36 eq1801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq7567 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1801 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1801
  have eq7579 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7550 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq7550
    | (have j0 := eq7550 X0 X1
       grind)
    | exact resolve eq7550 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7550
  have eq7645 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7579 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq7579
    | (have j0 := eq7579 X0 X1
       grind)
    | exact resolve eq7579 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7579
  have eq8762 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (k X0 X0)) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X2 X1
       have i₂ := eq7645 X2 X0
       grind)
    | exact superpose eq7645 eq57
    | (have j1 := eq7645 X1 (M.op X2 (k X0 X0))
       grind)
    | exact resolve eq57 eq7645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq8897 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq7645 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7645
  have eq9010 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8897 X1 (τ X0)
       have i₂ := eq1571 X0 X0
       grind)
    | exact superpose eq1571 eq8897
    | (have j0 := eq8897 X1 (τ X0)
       grind)
    | exact resolve eq8897 eq1571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1571 eq8897
  have eq51308 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op x (M.op (M.op X1 X2) (M.op x y)))) X1) = (M.op (M.op X0 (M.op x (M.op (M.op X1 X2) (M.op x y)))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1224 X0 X1 X2 X2
       have i₂ := eq215 X0 (M.op X1 X2) X2
       grind)
    | (have i₁ := eq1224 x X1 X2 y
       have i₂ := eq215 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq215 eq1224
    | exact resolve eq1224 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224
  have eq51309 : ∀ X1 X2 : G, (k (M.op x (M.op (M.op X1 X2) (M.op x y))) X1) = (M.op (M.op x (M.op (M.op X1 X2) (M.op x y))) X1) := by
    intro X1 X2
    first
    | exact superpose eq3236 eq51308
    | exact resolve eq51308 eq3236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3236 eq51308
  have eq51476 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | exact superpose eq1432 eq51309
    | (have j1 := eq1432 X1 X0
       grind)
    | exact resolve eq51309 eq1432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1432 eq51309
  have eq59602 : ∀ X0 X1 : G, (M.op X0 (k X1 X1)) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq8762 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59756 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X2 ∨ (M.op X1 X1) = X2 ∨ (M.op X1 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59602 X1 X2
       have i₂ := eq8762 X2 X0 X1
       grind)
    | (have i₁ := eq59602 (k X1 X1) X1
       have i₂ := eq8762 X0 (k X1 X1) X2
       grind)
    | exact superpose eq8762 eq59602
    | (have j0 := eq59602 X1 X2
       have j1 := eq8762 X2 X1 X1
       grind)
    | (have r₁ := eq59602 (k (M.op X2 (k X0 X0)) (M.op X2 (k X0 X0))) (M.op X2 (k X0 X0))
       have r₂ := eq8762 X0 (k (M.op X2 (k X0 X0)) (M.op X2 (k X0 X0))) X2
       grind)
    | (have r₁ := eq59602 X2 (M.op X1 X1)
       have r₂ := eq8762 (M.op X1 X1) X1 X2
       grind)
    | (have r₁ := eq59602 (k X0 X0) X0
       have r₂ := eq8762 X0 X1 (k X0 X0)
       grind)
    | exact resolve eq59602 eq8762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8762 eq59602
  have eq59838 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X2 ∨ (M.op X1 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq59756 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59756
  have eq125472 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq94 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125481 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq125472
    | exact resolve eq125472 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125472
  have eq125492 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq125481
       have r₂ := eq29
       grind)
    | exact resolve eq125481 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125481
  have eq125494 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq125492
       have i₂ := eq253 sF2 x
       grind)
    | (have i₁ := eq125492
       have i₂ := eq253 X0 sF2
       grind)
    | exact superpose eq253 eq125492
    | exact resolve eq125492 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125492
  have eq125817 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op X0 X0) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    intro X0
    grind
  clear eq125494
  have eq126116 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op X0 X0) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq28 eq125817
    | (have j0 := eq125817 X0
       grind)
    | exact resolve eq125817 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125817
  have eq127078 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (M.op X0 X0) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq126116 eq94
    | (have j1 := eq126116 X0
       grind)
    | exact resolve eq94 eq126116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq126116
  have eq127096 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq127078 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127078
  have eq127098 : ∀ X0 : G, y = (M.op x x) ∨ x = (M.op y y) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq127096 X0
       grind)
    | (have r₁ := eq127096 X0
       have r₂ := eq29
       grind)
    | exact resolve eq127096 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127096
  have eq127100 : ∀ X0 X1 : G, x = (M.op y y) ∨ (M.op X0 X0) = y ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq127098 X1
       have i₂ := eq253 x X0
       grind)
    | (have i₁ := eq127098 X1
       have i₂ := eq253 X0 x
       grind)
    | exact superpose eq253 eq127098
    | (have j0 := eq127098 X1
       grind)
    | exact resolve eq127098 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127098
  have eq127417 : ∀ X0 X1 X2 : G, (σ y) = (M.op X2 X2) ∨ (M.op X1 X1) = y ∨ (M.op X0 X0) = x := by
    intro X0 X1 X2
    first
    | (have i₁ := eq127100 X1 X2
       have i₂ := eq253 y X0
       grind)
    | (have i₁ := eq127100 X1 X2
       have i₂ := eq253 X0 y
       grind)
    | exact superpose eq253 eq127100
    | (have j0 := eq127100 X1 X2
       grind)
    | exact resolve eq127100 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127100
  have eq128764 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = y ∨ (M.op X1 X1) = x := by
    intro X0 X1
    first
    | (have i₁ := eq54 sF4
       have i₂ := eq127417 X0 X1 sF4
       grind)
    | (have i₁ := eq54 sF4
       have i₂ := eq127417 X0 sF4 x
       grind)
    | exact superpose eq127417 eq54
    | (have j1 := eq127417 X1 X0 x
       grind)
    | exact resolve eq54 eq127417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127417
  have eq128817 : ∀ X0 X1 : G, (M.op X1 X1) = x ∨ (M.op X0 X0) = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq28 eq128764
    | (have j0 := eq128764 X0 X1
       grind)
    | exact resolve eq128764 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128764
  have eq129414 : ∀ X1 X2 : G, y = (M.op X2 X2) ∨ x = (M.op X1 x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1 X2
    first
    | (have i₁ := eq56 x (M.op x x) X2
       have i₂ := eq128817 x (M.op x x)
       grind)
    | exact superpose eq128817 eq56
    | (have j1 := eq128817 X2 X1
       grind)
    | exact resolve eq56 eq128817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128817
  have eq130374 : ∀ X0 : G, y = (M.op x y) ∨ x = (M.op X0 x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq53 sF0
       have i₂ := eq129414 x sF0
       grind)
    | exact superpose eq129414 eq53
    | (have j1 := eq129414 X0 x
       grind)
    | exact resolve eq53 eq129414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129414
  have eq130519 : ∀ X0 : G, x = (M.op X0 x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq130374 X0
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq130374
    | (have j0 := eq130374 X0
       grind)
    | exact resolve eq130374 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130374
  have eq130724 : ∀ X0 : G, (M.op X0 X0) = x ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq130519 x
       have i₂ := eq253 x X0
       grind)
    | (have i₁ := eq130519 x
       have i₂ := eq253 X0 x
       grind)
    | exact superpose eq253 eq130519
    | exact resolve eq130519 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130731 : (k x x) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq130758 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1127 x x
       have i₂ := eq130519 x
       grind)
    | exact superpose eq130519 eq1127
    | exact resolve eq1127 eq130519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130519
  have eq134043 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq130731
       grind)
    | exact superpose eq130731 eq45
    | exact resolve eq45 eq130731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq130731
  have eq136113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq46
       have i₂ := eq130758 y
       grind)
    | exact superpose eq130758 eq46
    | exact resolve eq46 eq130758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq130758
  have eq136140 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq136113
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq136113
    | exact resolve eq136113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136113
  have eq136253 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22 eq136140
    | exact resolve eq136140 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136140
  have eq143582 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq134043
       have i₂ := eq130724 x
       grind)
    | exact superpose eq130724 eq134043
    | exact resolve eq134043 eq130724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130724 eq134043
  have eq143685 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq143582
  have eq143747 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq143685
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq143685
    | exact resolve eq143685 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq143685
  have eq143850 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq143747 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq143747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143747
  have eq143867 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq143850
  have eq143953 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq143867 eq1127
    | exact resolve eq1127 eq143867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127 eq143867
  have eq153680 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq143953 eq136253
    | exact resolve eq136253 eq143953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136253 eq143953
  have eq153681 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq153680
  have eq153695 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq153681
    | exact resolve eq153681 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153681
  have eq153802 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq153695
       have r₂ := eq29
       grind)
    | exact resolve eq153695 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153695
  have eq153870 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq153802 eq54
    | exact resolve eq54 eq153802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq154035 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq153870
    | (have j0 := eq153870 (σ x)
       grind)
    | exact resolve eq153870 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153870
  have eq154686 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq153802 eq154035
    | exact resolve eq154035 eq153802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154035
  have eq154716 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq154686
  have eq154718 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq154716
    | exact resolve eq154716 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154716
  have eq154727 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq154718
       have i₂ := eq253 sF2 x
       grind)
    | (have i₁ := eq154718
       have i₂ := eq253 X0 sF2
       grind)
    | exact superpose eq253 eq154718
    | exact resolve eq154718 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154760 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq154718 eq439
    | exact resolve eq439 eq154718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq154907 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq154718 eq59838
    | (have j0 := eq59838 X0 X1 X0
       grind)
    | (have r₁ := eq59838 (σ x) X1 (M.op (σ x) (σ y))
       have r₂ := eq154718
       grind)
    | exact resolve eq59838 eq154718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59838 eq154718
  have eq155093 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X1 X1)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq154727 X0
       have i₂ := eq262 X1 X0
       grind)
    | (have i₁ := eq154727 (M.op X0 X0)
       have i₂ := eq262 X0 (M.op X0 X0)
       grind)
    | exact superpose eq262 eq154727
    | exact resolve eq154727 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155542 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op X1 (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq56 x (M.op x x) x
       have i₂ := eq154727 (M.op x x)
       grind)
    | exact superpose eq154727 eq56
    | exact resolve eq56 eq154727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq154727
  have eq162209 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X1 (M.op X0 (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq155093 X1 x
       have i₂ := eq154760 x X0
       grind)
    | (have i₁ := eq155093 X0 (M.op (σ x) (σ y))
       have i₂ := eq154760 X0 (M.op (σ x) (σ y))
       grind)
    | exact superpose eq154760 eq155093
    | exact resolve eq155093 eq154760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154760 eq155093
  have eq163023 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X1 (M.op X0 (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq162209 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162209
  have eq214887 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq155542 eq51476
    | exact resolve eq51476 eq155542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51476 eq155542
  have eq215730 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq214887 X0
       have j1 := eq154907 (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0
       grind)
    | (have r₁ := eq214887 X0
       have r₂ := eq154907 (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) x
       grind)
    | exact resolve eq214887 eq154907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154907 eq214887
  have eq216490 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq163023 x (M.op x sF4)
       have i₂ := eq215730 (M.op x sF4)
       grind)
    | exact superpose eq215730 eq163023
    | exact resolve eq163023 eq215730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163023 eq215730
  have eq216669 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq216490
  have eq216791 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq153802 eq216669
    | exact resolve eq216669 eq153802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153802 eq216669
  have eq216878 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq216791
  have eq217037 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (M.op X0 X0) = (τ (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq216878 eq9010
    | (have j0 := eq9010 (σ y) X0
       grind)
    | exact resolve eq9010 eq216878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9010 eq216878
  have eq217081 : ∀ X0 : G, (M.op X0 X0) = (τ (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq217037 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217037
  have eq217111 : ∀ X0 : G, (M.op X0 X0) = y ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq31 eq217081
    | exact resolve eq217081 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq217081
  have eq217882 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq53 sF0
       have i₂ := eq217111 sF0
       grind)
    | exact superpose eq217111 eq53
    | exact resolve eq53 eq217111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq217111
  have eq218220 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq217882
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq217882
    | exact resolve eq217882 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217882
  have eq218221 : y = (M.op x y) := by grind
  clear eq218220
  have eq218425 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq218221 eq22
    | exact resolve eq22 eq218221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq218643 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq218425
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq218425
    | exact resolve eq218425 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218425
  have eq218652 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq218643 eq28
    | exact resolve eq28 eq218643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq218904 : ∀ X0 X1 X3 X4 : G, (M.op X3 (M.op X0 (M.op X1 X1))) = (M.op x (M.op (M.op X3 X4) (M.op x y))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq725 X0 X1 x X3 X4 x
       have i₂ := eq215 x (M.op X3 X4) x
       grind)
    | (have i₁ := eq725 X0 X1 x X3 X4 y
       have i₂ := eq215 X0 (M.op X3 X4) x
       grind)
    | exact superpose eq215 eq725
    | (have j0 := eq725 X0 X1 x X3 X4 y
       grind)
    | exact resolve eq725 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq725
  have eq218905 : ∀ X0 X1 X3 X4 : G, (M.op X3 (M.op X0 (M.op X1 X1))) = (M.op x (M.op (M.op X3 X4) y)) := by
    intro X0 X1 X3 X4
    first
    | exact superpose eq218221 eq218904
    | exact resolve eq218904 eq218221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218904
  have eq218906 : ∀ X0 X3 X4 : G, (M.op x (M.op X0 (M.op x y))) = (M.op x (M.op (M.op X3 X4) y)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq218905 X0 x X3 X4
       have i₂ := eq420 X0 X3 x
       grind)
    | exact superpose eq420 eq218905
    | exact resolve eq218905 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420 eq218905
  have eq218907 : ∀ X0 X3 X4 : G, (M.op x (M.op X0 y)) = (M.op x (M.op (M.op X3 X4) y)) := by
    intro X0 X3 X4
    first
    | exact superpose eq218221 eq218906
    | exact resolve eq218906 eq218221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218906
  have eq219281 : ∀ X0 : G, (M.op x (M.op X0 y)) = (M.op x (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq218907 X0 x y
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq218907
    | (have j0 := eq218907 X0 x y
       grind)
    | exact resolve eq218907 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218907
  have eq219391 : ∀ X0 : G, (M.op x (M.op X0 y)) = (M.op x (M.op y y)) := by
    intro X0
    first
    | exact superpose eq218221 eq219281
    | exact resolve eq219281 eq218221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219281
  have eq219466 : ∀ X0 : G, (M.op x x) = (M.op x (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq219391 X0
       have i₂ := eq262 y x
       grind)
    | exact superpose eq262 eq219391
    | exact resolve eq219391 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219391
  have eq219587 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq219466 x
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq219466
    | (have j0 := eq219466 x
       grind)
    | exact resolve eq219466 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219692 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq218221 eq219587
    | exact resolve eq219587 eq218221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219587
  have eq219698 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq219692
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq219692
    | exact resolve eq219692 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq219692
  have eq219700 : y = (M.op x x) := by
    first
    | exact superpose eq218221 eq219698
    | exact resolve eq219698 eq218221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219698
  have eq219709 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq219700
       have i₂ := eq253 x X0
       grind)
    | (have i₁ := eq219700
       have i₂ := eq253 X0 x
       grind)
    | exact superpose eq253 eq219700
    | exact resolve eq219700 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq219758 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op x y))) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq667 X0 X1 x
       have i₂ := eq219700
       grind)
    | exact superpose eq219700 eq667
    | exact resolve eq667 eq219700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq220099 : ∀ X0 X1 : G, (M.op X1 y) = (M.op x (M.op X0 y)) := by
    intro X0 X1
    first
    | exact superpose eq218221 eq219758
    | exact resolve eq219758 eq218221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218221 eq219758
  have eq220191 : ∀ X1 : G, (M.op x x) = (M.op X1 y) := by
    intro X1
    first
    | (have i₁ := eq220099 x X1
       have i₂ := eq219466 x
       grind)
    | exact superpose eq219466 eq220099
    | exact resolve eq220099 eq219466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219466 eq220099
  have eq220263 : ∀ X1 : G, y = (M.op X1 y) := by
    intro X1
    first
    | (have i₁ := eq220191 X1
       have i₂ := eq219700
       grind)
    | exact superpose eq219700 eq220191
    | exact resolve eq220191 eq219700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219700 eq220191
  have eq220923 : ∀ X0 : G, (k y (M.op X0 X0)) = (M.op y (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1097 X0 (M.op X0 X0)
       have i₂ := eq219709 (M.op X0 X0)
       grind)
    | exact superpose eq219709 eq1097
    | exact resolve eq1097 eq219709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097
  have eq221427 : ∀ X0 : G, (M.op y y) = (k y (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq220923 X0
       have i₂ := eq262 X0 y
       grind)
    | exact superpose eq262 eq220923
    | exact resolve eq220923 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262 eq220923
  have eq221998 : (k y y) = (M.op y y) := by
    first
    | (have i₁ := eq221427 x
       have i₂ := eq219709 x
       grind)
    | exact superpose eq219709 eq221427
    | exact resolve eq221427 eq219709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221427
  have eq222400 : y = (k y y) := by
    first
    | (have i₁ := eq221998
       have i₂ := eq219709 y
       grind)
    | exact superpose eq219709 eq221998
    | exact resolve eq221998 eq219709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221998
  have eq223874 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq7567 X0 y
       have i₂ := eq222400
       grind)
    | exact superpose eq222400 eq7567
    | (have j0 := eq7567 X0 y
       grind)
    | exact resolve eq7567 eq222400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7567 eq222400
  have eq223930 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq223874 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223874
  have eq223954 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq223930 X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq223930
    | (have j0 := eq223930 X0
       grind)
    | exact resolve eq223930 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq223930
  have eq223985 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq218643 eq223954
    | exact resolve eq223954 eq218643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218643 eq223954
  have eq224015 : y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq223985 x
       have i₂ := eq219709 x
       grind)
    | exact superpose eq219709 eq223985
    | exact resolve eq223985 eq219709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219709 eq223985
  have eq224179 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq224015 eq218652
    | exact resolve eq218652 eq224015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218652
  have eq224180 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq224179
       have i₂ := eq220263 sF2
       grind)
    | exact superpose eq220263 eq224179
    | exact resolve eq224179 eq220263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220263 eq224179
  have eq224391 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq224180 eq29
    | exact resolve eq29 eq224180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq224180
  have eq224432 : False := by grind
  exact eq224432
