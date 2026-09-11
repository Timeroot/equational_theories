import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4381`: `x ◇ (x ◇ x) = (x ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxx_x_pyx_Equation4381 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4381 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4381.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
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
  have eq19 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19
    | exact resolve eq19 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X1
       have i₂ := eq9 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq9 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq9 eq46
    | exact resolve eq46 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq50 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq52 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq58 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq52 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq59 : ∀ X0 : G, (k X0 X0) = X0 := by
    intro X0
    grind
  clear eq58
  have eq66 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq49 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq49 eq12
    | (have j0 := eq12 X1 (M.op X0 (M.op X0 X0))
       grind)
    | (have r₁ := eq12 X0 (M.op X0 (M.op X0 X0))
       have r₂ := eq49 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq12 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq77 : ∀ X0 X1 : G, (k (τ X1) (τ (M.op X0 (M.op X0 X0)))) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq24
    | exact resolve eq24 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, (k (σ X1) (σ (M.op X0 (M.op X0 X0)))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq15
    | exact resolve eq15 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq78
    | exact resolve eq78 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq77
    | exact resolve eq77 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : ∀ X0 X1 X2 : G, X1 ≠ X1 ∨ (M.op X2 X2) = (k X2 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X2 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq129 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq157 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (M.op X1 X1)))) = (k X0 (σ (M.op X2 (M.op X2 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81 X0 X2
       have i₂ := eq81 X0 X1
       grind)
    | exact superpose eq81 eq81
    | exact resolve eq81 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (τ (σ X1)) = (k X1 (τ (M.op X2 (M.op X2 X2)))) ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq103 X1 X2
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq103
    | (have j1 := eq14 (τ (σ X1)) (k X1 (τ (M.op X2 (M.op X2 X2))))
       grind)
    | exact resolve eq103 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 X1 X2 : G, (k X1 (τ (M.op X2 (M.op X2 X2)))) = X1 ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq177
    | (have j0 := eq177 X0 X1 X2
       grind)
    | exact resolve eq177 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq219 : ∀ X0 X1 X2 : G, (k (τ X1) (τ X2)) = (τ (M.op X2 X1)) ∨ X1 = X2 ∨ (M.op X0 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X2 X1
       have i₂ := eq138 X1 X2 X0
       grind)
    | exact superpose eq138 eq24
    | (have j1 := eq138 X1 X2 X0
       grind)
    | exact resolve eq24 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 X1 X2 : G, (k (σ X1) (σ X2)) = (σ (M.op X2 X1)) ∨ X1 = X2 ∨ (M.op X0 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X2
       have i₂ := eq138 X1 X2 X0
       grind)
    | exact superpose eq138 eq15
    | (have j1 := eq138 X1 X2 X0
       grind)
    | exact resolve eq15 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq1088 : ∀ X0 : G, x = y ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq220 X0 y x
       grind)
    | exact superpose eq220 eq16
    | (have j1 := eq220 X0 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq220 X0 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq220 X0 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1095 : ∀ X0 X1 X2 X3 : G, (k X2 (σ (M.op X3 (M.op X3 X3)))) = (k X2 (k (σ (M.op X0 X0)) (σ X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq157 X2 X3 X0
       have i₂ := eq220 X1 (M.op X0 X0) X0
       grind)
    | exact superpose eq220 eq157
    | (have j1 := eq220 X1 (M.op X0 X0) X0
       grind)
    | exact resolve eq157 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq1102 : ∀ X0 X1 X2 X3 : G, (σ (M.op (M.op X0 X2) (M.op X0 X2))) = (k (k (σ X2) (σ X0)) (σ (M.op X3 (M.op X3 X3)))) ∨ X0 = X2 ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq78 X3 (M.op X0 X2)
       have i₂ := eq220 X1 X2 X0
       grind)
    | exact superpose eq220 eq78
    | (have j1 := eq220 X0 (σ (M.op (M.op X0 X2) (M.op X0 X2))) (k (k (σ X2) (σ X0)) (σ (M.op X3 (M.op X3 X3))))
       grind)
    | exact resolve eq78 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq1117 : ∀ X0 X1 X2 X3 : G, (k X2 (σ (M.op X3 (M.op X3 X3)))) = (k X2 (k (σ (M.op X0 X0)) (σ X0))) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1095 X0 X1 X2 X3
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq1095 X1 X1 X2 X3
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1095 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095
  have eq1223 : ∀ X0 X1 X2 : G, (τ (M.op X2 X2)) = (k (τ X2) (k (τ (M.op X0 X0)) (τ X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq77 X0 X2
       have i₂ := eq219 X1 (M.op X0 X0) X0
       grind)
    | exact superpose eq219 eq77
    | (have j1 := eq219 X1 (M.op X0 X0) X0
       grind)
    | exact resolve eq77 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq219
  have eq1257 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (τ (M.op X2 X2)) = (k (τ X2) (k (τ (M.op X0 X0)) (τ X0))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1223 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq1223 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1223 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223
  have eq1847 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1088 X0
       grind)
    | exact superpose eq1088 eq16
    | (have j1 := eq1088 X0
       grind)
    | exact resolve eq16 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088
  have eq3566 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) = (k (τ X0) (k (τ (M.op X1 X1)) (τ X1))) ∨ (τ (M.op X2 X2)) = (k (τ X2) (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 X2
       have i₂ := eq1257 X1 X2 X0
       grind)
    | exact superpose eq1257 eq24
    | (have j1 := eq1257 X1 X1 X0
       grind)
    | exact resolve eq24 eq1257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257
  have eq7952 : ∀ X0 X2 : G, (τ (M.op (σ X0) (σ X0))) = X0 ∨ (σ X0) = X2 ∨ (k X2 (σ X0)) = (M.op (σ X0) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq194 X2 X0 x
       have i₂ := eq103 X0 x
       grind)
    | exact superpose eq103 eq194
    | (have j0 := eq194 X2 X0 X2
       grind)
    | exact resolve eq194 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq194
  have eq25803 : ∀ X0 X1 X2 X3 : G, (τ (k X2 (σ (M.op X1 (M.op X1 X1))))) = (k (τ X2) (τ (k (σ (M.op X0 X0)) (σ X0)))) ∨ (M.op X3 X3) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 (k (σ (M.op X0 X0)) (σ X0)) X2
       have i₂ := eq1117 X0 X3 X2 X1
       grind)
    | exact superpose eq1117 eq24
    | (have j1 := eq1117 X0 X3 X2 X3
       grind)
    | exact resolve eq24 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1117
  have eq25826 : ∀ X0 X1 X2 X3 : G, (τ (k X2 (σ (M.op X1 (M.op X1 X1))))) = (k (τ X2) (k (M.op X0 X0) X0)) ∨ (M.op X3 X3) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25803 X0 X1 X2 X3
       have i₂ := eq18 (M.op X0 X0) X0
       grind)
    | exact superpose eq18 eq25803
    | (have j0 := eq25803 X0 X1 X2 X3
       grind)
    | exact resolve eq25803 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25803
  have eq25864 : ∀ X0 X1 X2 X3 : G, (k (τ X2) (k (M.op X0 X0) X0)) = (k (τ X2) (M.op X1 (M.op X1 X1))) ∨ (M.op X3 X3) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25826 X0 X1 X2 X3
       have i₂ := eq19 X2 (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq19 eq25826
    | (have j0 := eq25826 X0 X1 X2 X3
       grind)
    | exact resolve eq25826 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25826
  have eq25875 : ∀ X0 X2 X3 : G, (M.op (τ X2) (τ X2)) = (k (τ X2) (k (M.op X0 X0) X0)) ∨ (M.op X3 X3) = (k X3 X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq25864 X0 x X2 X3
       have i₂ := eq68 x (τ X2)
       grind)
    | exact superpose eq68 eq25864
    | (have j0 := eq25864 (k (M.op X0 X0) X0) x X2 (τ X2)
       grind)
    | exact resolve eq25864 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25864
  have eq25905 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (k (M.op X1 X1) X1)) ∨ (M.op X2 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25875 X0 (σ X0) x
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25875
    | (have j0 := eq25875 (k (M.op X1 X1) X1) X2 X0
       grind)
    | exact resolve eq25875 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25875
  have eq26066 : ∀ X0 X1 : G, (k (M.op X1 X1) X1) = (M.op (k (M.op X1 X1) X1) (k (M.op X1 X1) X1)) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25905 (k (M.op X1 X1) X1) X1 X0
       have i₂ := eq59 (k (M.op X1 X1) X1)
       grind)
    | exact superpose eq59 eq25905
    | (have j0 := eq25905 X0 X1 X0
       grind)
    | exact resolve eq25905 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25905
  have eq28276 : ∀ X0 X1 X2 : G, (τ (M.op X2 X2)) = (k (τ X2) (k (τ (M.op (σ X0) (σ X0))) X0)) ∨ (τ (M.op X1 X1)) = (k (τ X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3566 X0 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3566
    | exact resolve eq3566 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3566
  have eq44335 : ∀ X0 X1 : G, (k (τ X0) X1) ≠ (k (τ X0) (k (τ (M.op (σ X1) (σ X1))) X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq28276 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28276
  have eq50828 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X0 (k (τ (M.op (σ X1) (σ X1))) X1)) ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq44335 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq44335
    | exact resolve eq44335 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44335
  have eq51204 : ∀ X0 X1 X2 : G, (k X2 X1) ≠ (k X2 (k X1 X1)) ∨ (k X2 X1) = (τ (M.op (σ X2) (σ X2))) ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50828 X2 X1
       have i₂ := eq7952 X1 X0
       grind)
    | exact superpose eq7952 eq50828
    | (have j0 := eq50828 X2 X1
       have j1 := eq7952 X1 X0
       grind)
    | exact resolve eq50828 eq7952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7952 eq50828
  have eq51274 : ∀ X0 X1 X2 : G, (k X2 X1) ≠ (k X2 X1) ∨ (k X2 X1) = (τ (M.op (σ X2) (σ X2))) ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51204 X0 X1 X2
       have i₂ := eq59 X1
       grind)
    | exact superpose eq59 eq51204
    | (have j0 := eq51204 X0 X1 X2
       grind)
    | exact resolve eq51204 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51204
  have eq51275 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 ∨ (k X2 X1) = (τ (M.op (σ X2) (σ X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq51274 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51274
  have eq62691 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X0 X2)) = (τ (k (k (σ X2) (σ X0)) (σ (M.op X1 (M.op X1 X1))))) ∨ X0 = X2 ∨ (M.op X3 X3) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10 (M.op (M.op X0 X2) (M.op X0 X2))
       have i₂ := eq1102 X0 X3 X2 X1
       grind)
    | exact superpose eq1102 eq10
    | (have j1 := eq1102 X0 X3 X2 X3
       grind)
    | exact resolve eq10 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq62806 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X0 X2)) = (k (τ (k (σ X2) (σ X0))) (M.op X1 (M.op X1 X1))) ∨ X0 = X2 ∨ (M.op X3 X3) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62691 X0 X1 X2 X3
       have i₂ := eq19 (k (σ X2) (σ X0)) (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq19 eq62691
    | (have j0 := eq62691 X0 X1 X2 X3
       grind)
    | exact resolve eq62691 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq62691
  have eq62861 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) (M.op X0 X2)) = (M.op (τ (k (σ X2) (σ X0))) (τ (k (σ X2) (σ X0)))) ∨ X0 = X2 ∨ (M.op X3 X3) = (k X3 X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq62806 X0 x X2 X3
       have i₂ := eq68 x (τ (k (σ X2) (σ X0)))
       grind)
    | exact superpose eq68 eq62806
    | (have j0 := eq62806 X0 x X2 X3
       grind)
    | exact resolve eq62806 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62806
  have eq62891 : ∀ X0 X2 X3 : G, (M.op X3 X3) = (k X3 X0) ∨ X0 = X2 ∨ (M.op (M.op X0 X2) (M.op X0 X2)) = (M.op (k X2 X0) (k X2 X0)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq62861 x X0 X3
       have i₂ := eq18 X0 x
       grind)
    | exact superpose eq18 eq62861
    | (have j0 := eq62861 X0 X2 X3
       grind)
    | exact resolve eq62861 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq62861
  have eq62903 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ X0 = X1 ∨ (M.op (k X1 X0) (k X1 X0)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq62891 X0 X1 X0
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq62891
    | (have j0 := eq62891 X0 X1 x
       grind)
    | exact resolve eq62891 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62891
  have eq63831 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq62903 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62903
  have eq63832 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq63831 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63831
  have eq63835 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (M.op X0 X0)) = (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq63832 X0
       have i₂ := eq49 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq49 eq63832
    | (have j0 := eq63832 X0
       grind)
    | exact resolve eq63832 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq63832
  have eq63983 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 (M.op X0 X0)) = (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq63835 X0
       grind)
    | exact superpose eq63835 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq63835 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq63835 X0
       grind)
    | exact resolve eq12 eq63835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63835
  have eq64363 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq63983 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63983
  have eq65133 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X2 X2) = (k X2 X0) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26066 X2 X0
       have i₂ := eq64363 X0 X1
       grind)
    | exact superpose eq64363 eq26066
    | (have j0 := eq26066 X2 X0
       have j1 := eq64363 X0 X2
       grind)
    | exact resolve eq26066 eq64363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26066 eq64363
  have eq65416 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq65133 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65133
  have eq65705 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq65416 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65416
  have eq65736 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq65705 X0
       grind)
    | (have r₁ := eq65705 X0
       have r₂ := eq9 X0 (M.op X0 X0)
       grind)
    | exact resolve eq65705 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65705
  have eq65762 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq65736 X0
       have i₂ := eq9 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq65736
    | exact resolve eq65736 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65736
  have eq65786 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65762 (M.op X0 X0)
       have i₂ := eq9 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq65762
    | exact resolve eq65762 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65872 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 (M.op X0 X0) X0
       have i₂ := eq65762 X0
       grind)
    | exact superpose eq65762 eq15
    | exact resolve eq15 eq65762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65960 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65786 X0
       have i₂ := eq9 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq9 eq65786
    | exact resolve eq65786 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65786
  have eq66009 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (k (σ X1) (k (σ (M.op X0 X0)) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 X1
       have i₂ := eq65872 X0
       grind)
    | exact superpose eq65872 eq78
    | exact resolve eq78 eq65872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq66010 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (k X1 (k (σ (M.op X0 X0)) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X1 X0
       have i₂ := eq65872 X0
       grind)
    | exact superpose eq65872 eq81
    | exact resolve eq81 eq65872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq66696 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (k (σ X1) (k (σ (M.op (τ X0) (τ X0))) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq66009 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq66009
    | exact resolve eq66009 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66009
  have eq67991 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = (k (σ X2) (k (k X1 (k (σ (M.op X0 X0)) (σ X0))) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66696 X1 X2
       have i₂ := eq66010 X0 X1
       grind)
    | exact superpose eq66010 eq66696
    | exact resolve eq66696 eq66010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66010 eq66696
  have eq71631 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (k (σ X1) (k (M.op (k (σ (M.op X0 X0)) (σ X0)) (M.op (k (σ (M.op X0 X0)) (σ X0)) (k (σ (M.op X0 X0)) (σ X0)))) (M.op (k (σ (M.op X0 X0)) (σ X0)) (k (σ (M.op X0 X0)) (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq67991 X0 (M.op (k (σ (M.op X0 X0)) (σ X0)) (k (σ (M.op X0 X0)) (σ X0))) X1
       have i₂ := eq65762 (k (σ (M.op X0 X0)) (σ X0))
       grind)
    | exact superpose eq65762 eq67991
    | exact resolve eq67991 eq65762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65762 eq67991
  have eq71781 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (k (σ X1) (M.op (k (σ (M.op X0 X0)) (σ X0)) (M.op (k (σ (M.op X0 X0)) (σ X0)) (k (σ (M.op X0 X0)) (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq71631 X0 X1
       have i₂ := eq65960 (k (σ (M.op X0 X0)) (σ X0))
       grind)
    | exact superpose eq65960 eq71631
    | exact resolve eq71631 eq65960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65960 eq71631
  have eq71852 : ∀ X1 : G, (σ (M.op X1 X1)) = (M.op (σ X1) (σ X1)) := by
    intro X1
    first
    | (have i₁ := eq71781 x X1
       have i₂ := eq68 (k (σ (M.op x x)) (σ x)) (σ X1)
       grind)
    | exact superpose eq68 eq71781
    | exact resolve eq71781 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq71781
  have eq71925 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq1847 X0
       grind)
    | (have r₁ := eq1847 X0
       have r₂ := eq71852 x
       grind)
    | exact resolve eq1847 eq71852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1847
  have eq71999 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq71852 X0
       grind)
    | exact superpose eq71852 eq10
    | exact resolve eq10 eq71852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72278 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq71999 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq71999
    | exact resolve eq71999 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71999
  have eq72677 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op X1 X1) = (k X1 x) ∨ (σ x) = (σ y) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq71925 X1
       have i₂ := eq51275 (σ y) x X0
       grind)
    | exact superpose eq51275 eq71925
    | (have j0 := eq71925 X1
       have j1 := eq51275 (σ y) x X0
       grind)
    | (have r₁ := eq71925 X0
       have r₂ := eq51275 (σ y) x x
       grind)
    | exact resolve eq71925 eq51275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51275 eq71925
  have eq72698 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 x) ∨ (σ x) = (σ y) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 x) := by
    intro X0 X1
    first
    | (have j0 := eq72677 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72677
  have eq72706 : ∀ X0 X1 : G, (M.op (τ (σ X0)) (τ (σ X0))) = (k X0 x) ∨ (M.op X1 X1) = (k X1 x) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq72698 X0 X1
       have i₂ := eq72278 (σ X0)
       grind)
    | exact superpose eq72278 eq72698
    | (have j0 := eq72698 X0 X1
       grind)
    | exact resolve eq72698 eq72278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72278 eq72698
  have eq72711 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 x) ∨ (M.op X1 X1) = (k X1 x) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq72706 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq72706
    | (have j0 := eq72706 X0 X0
       grind)
    | exact resolve eq72706 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72706
  have eq72712 : ∀ X1 : G, (M.op X1 X1) = (k X1 x) ∨ (σ x) = (σ y) := by
    intro X1
    first
    | (have j0 := eq72711 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72711
  have eq72715 : (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72712 x
       have i₂ := eq59 x
       grind)
    | exact superpose eq59 eq72712
    | exact resolve eq72712 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72712
  have eq72748 : y = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq72715
       grind)
    | exact superpose eq72715 eq10
    | exact resolve eq10 eq72715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72715
  have eq72761 : x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72748
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq72748
    | exact resolve eq72748 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72748
  have eq72767 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq72761
       grind)
    | exact superpose eq72761 eq16
    | exact resolve eq16 eq72761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72761
  have eq72770 : x = (M.op x x) := by
    first
    | (have r₁ := eq72767
       have r₂ := eq71852 x
       grind)
    | exact resolve eq72767 eq71852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72767
  have eq72772 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq9 x x
       have i₂ := eq72770
       grind)
    | exact superpose eq72770 eq9
    | exact resolve eq9 eq72770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72795 : (σ (M.op x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq65872 x
       have i₂ := eq72770
       grind)
    | exact superpose eq72770 eq65872
    | exact resolve eq65872 eq72770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65872
  have eq72803 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq72795
       have i₂ := eq59 (σ x)
       grind)
    | exact superpose eq59 eq72795
    | exact resolve eq72795 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq72795
  have eq72815 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq72772 X0
       have i₂ := eq72770
       grind)
    | exact superpose eq72770 eq72772
    | exact resolve eq72772 eq72770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72770 eq72772
  have eq72818 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq72803
       have i₂ := eq71852 x
       grind)
    | exact superpose eq71852 eq72803
    | exact resolve eq72803 eq71852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71852 eq72803
  have eq72828 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq72815 y
       grind)
    | exact superpose eq72815 eq16
    | exact resolve eq16 eq72815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72815
  have eq73027 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (σ x) x
       have i₂ := eq72818
       grind)
    | exact superpose eq72818 eq9
    | exact resolve eq9 eq72818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73071 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq73027 X0
       have i₂ := eq72818
       grind)
    | exact superpose eq72818 eq73027
    | exact resolve eq73027 eq72818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72818 eq73027
  have eq73141 : False := by grind
  exact eq73141

/-- `Equation4393`: `x ◇ (x ◇ x) = (y ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_x_x_pyx_Equation4393 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4393 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4393.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X2) := by
    intro X0 X1 X2
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq13 X0 (k (M.op X0 X0) X1)
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y
       grind)
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq45
    | exact resolve eq45 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq142 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq175 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : x ≠ (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : (σ y) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq37 (M.op y y)
       have i₂ := eq175 y
       grind)
    | exact superpose eq175 eq37
    | exact resolve eq37 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq182 : (σ y) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq179
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq179
    | exact resolve eq179 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq191 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq91 (M.op sF2 sF2)
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq91
    | exact resolve eq91 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq202 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq30 eq191
    | exact resolve eq191 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq209 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq108 (M.op sF3 sF3)
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq108
    | exact resolve eq108 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq175
  have eq220 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq32 eq209
    | exact resolve eq209 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq399 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq692 : ∀ X0 X1 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X0 (M.op X0 X0)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X1 (M.op x X3) X3
       have i₂ := eq16 X0 x X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq694 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698 : ∀ X1 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X3) := by
    intro X1 X3
    first
    | (have i₁ := eq692 x X1 X3
       have i₂ := eq694 x
       grind)
    | exact superpose eq694 eq692
    | exact resolve eq692 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq700 : ∀ X3 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X3) := by
    intro X3
    first
    | (have i₁ := eq698 x X3
       have i₂ := eq694 x
       grind)
    | exact superpose eq694 eq698
    | exact resolve eq698 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq702 : ∀ X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op (M.op x y) y) := by
    intro X1 X2
    first
    | (have i₁ := eq16 x X1 X2
       have i₂ := eq693 x
       grind)
    | exact superpose eq693 eq16
    | exact resolve eq16 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq693 x
       have i₂ := eq694 x
       grind)
    | exact superpose eq694 eq693
    | exact resolve eq693 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq719 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq708 eq700
    | exact resolve eq700 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq730 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq700 eq28
    | (have j0 := eq28 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | (have r₁ := eq28 x (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq700 x
       grind)
    | exact resolve eq28 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq733 : ∀ X0 : G, (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq730 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq735 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | exact superpose eq708 eq733
    | exact resolve eq733 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq744 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq735 eq399
    | exact resolve eq399 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq745 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq735 eq35
    | exact resolve eq35 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq758 : ∀ X0 : G, (k X0 (σ (M.op (M.op x y) y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq745 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq745
    | exact resolve eq745 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq759 : ∀ X0 : G, (k X0 (τ (M.op (M.op x y) y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq744 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq744
    | exact resolve eq744 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq764 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq765 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq768 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq693 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq693
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq693 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq772 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X2)) = (M.op (k X0 X1) X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq788 : x = (k x (τ (k (σ x) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq202
       have i₂ := eq11 sF2 sF2
       grind)
    | exact superpose eq11 eq202
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq202 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq792 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq793 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq794 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq793 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793
  have eq796 : x = (k x (τ (k (σ x) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq788
  have eq806 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq768 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq811 : x = (k x (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq98 eq796
    | exact resolve eq796 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq796
  have eq825 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (k X0 X1) X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq772 X0 X1 x
       have i₂ := eq694 x
       grind)
    | exact superpose eq694 eq772
    | (have j0 := eq772 X0 X1 x
       grind)
    | exact resolve eq772 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694 eq772
  have eq841 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op (k X0 X1) X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq708 eq825
    | (have j0 := eq825 X0 X1
       grind)
    | exact resolve eq825 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq1882 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq764
       grind)
    | exact superpose eq764 eq40
    | exact resolve eq40 eq764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1884 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1882
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1882
    | exact resolve eq1882 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1882
  have eq1886 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1884
    | exact resolve eq1884 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1884
  have eq1928 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1886 eq765
    | exact resolve eq765 eq1886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1936 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1928
       have r₂ := eq27
       grind)
    | exact resolve eq1928 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1928
  have eq1954 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq792 (σ X1) (σ X0)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq792
    | (have j0 := eq792 (σ X1) (σ X0)
       grind)
    | exact resolve eq792 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2017 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1936 eq220
    | exact resolve eq220 eq1936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq2032 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1936 eq702
    | exact resolve eq702 eq1936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2035 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26 eq2032
    | exact resolve eq2032 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2032
  have eq2046 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq2017
    | exact resolve eq2017 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2017
  have eq2055 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq2046
       have r₂ := eq176
       grind)
    | exact resolve eq2046 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq2046
  have eq2058 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq2055
       have r₂ := eq13 y x
       grind)
    | exact resolve eq2055 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2055
  have eq2060 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq764
       have i₂ := eq2058
       grind)
    | exact superpose eq2058 eq764
    | exact resolve eq764 eq2058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2062 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq2058
       grind)
    | exact superpose eq2058 eq40
    | exact resolve eq40 eq2058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058
  have eq2065 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2062
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2062
    | exact resolve eq2062 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2062
  have eq2068 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq2065
       have r₂ := eq177
       grind)
    | exact resolve eq2065 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq2065
  have eq2072 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2068 eq1886
    | exact resolve eq1886 eq2068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886
  have eq2073 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2068 eq765
    | exact resolve eq765 eq2068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq2076 : (τ (σ y)) = (k (τ (σ y)) x) := by
    first
    | exact superpose eq2068 eq142
    | exact resolve eq142 eq2068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2079 : y = (k y x) := by
    first
    | exact superpose eq32 eq2076
    | exact resolve eq2076 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2076
  have eq2084 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq764
       have i₂ := eq2079
       grind)
    | exact superpose eq2079 eq764
    | exact resolve eq764 eq2079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764 eq2079
  have eq2093 : x = (k y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2072
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq2072
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq2072 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2103 : x = (k y y) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq2072
       grind)
    | exact superpose eq2072 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq2072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2109 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq702 y y
       have i₂ := eq2072
       grind)
    | exact superpose eq2072 eq702
    | exact resolve eq702 eq2072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2110 : x = (k y y) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2103
  have eq2111 : x = (k y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq2093
  have eq2112 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2109
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2109
    | exact resolve eq2109 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2109
  have eq2123 : x = (k y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2110 eq2111
    | exact resolve eq2111 eq2110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2110 eq2111
  have eq2133 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq2073
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq2073
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq2073 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2143 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2073 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq2073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2149 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2073 eq702
    | exact resolve eq702 eq2073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2150 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2143
  have eq2151 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq2133
  have eq2152 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq2149
    | exact resolve eq2149 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2149
  have eq2163 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2150 eq2151
    | exact resolve eq2151 eq2150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2150 eq2151
  have eq2183 : x = (k y y) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq2084
       grind)
    | exact superpose eq2084 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq2084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2189 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq702 y y
       have i₂ := eq2084
       grind)
    | exact superpose eq2084 eq702
    | exact resolve eq702 eq2084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084
  have eq2190 : x = (k y y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2183
  have eq2192 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2189
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2189
    | exact resolve eq2189 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2189
  have eq2225 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq2112 eq758
    | exact resolve eq758 eq2112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2282 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq20 eq2225
    | (have j0 := eq2225 X0
       grind)
    | exact resolve eq2225 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2225
  have eq2338 : (M.op x y) ≠ (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2152 eq28
    | (have j0 := eq28 y (M.op x y)
       grind)
    | (have r₁ := eq28 (σ y) (σ x)
       have r₂ := eq2152
       grind)
    | exact resolve eq28 eq2152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2362 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2192 eq719
    | exact resolve eq719 eq2192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2363 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2192 eq735
    | exact resolve eq735 eq2192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2595 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2282 eq794
    | (have j0 := eq794 (σ (M.op x y))
       grind)
    | (have r₁ := eq794 (σ (M.op x y))
       have r₂ := eq2282 (σ (M.op x y))
       grind)
    | exact resolve eq794 eq2282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2282
  have eq2610 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2595
  have eq2929 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2610 eq702
    | exact resolve eq702 eq2610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2932 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2112 eq2929
    | exact resolve eq2929 eq2112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2112 eq2929
  have eq3093 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2932 eq2610
    | exact resolve eq2610 eq2932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2610 eq2932
  have eq3112 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq3093
  have eq3144 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq3112 eq29
    | exact resolve eq29 eq3112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq3166 : (M.op x y) ≠ (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  have eq3179 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq3144
    | exact resolve eq3144 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq3144
  have eq4422 : (M.op (σ y) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq2068 eq841
    | (have j0 := eq841 (σ y) (σ x)
       grind)
    | exact resolve eq841 eq2068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2068
  have eq4443 : (M.op (σ y) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq4422
    | exact resolve eq4422 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4422
  have eq8282 : ∀ X0 : G, x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq2035 eq735
    | exact resolve eq735 eq2035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8562 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq702 y y
       have i₂ := eq8282 X0
       grind)
    | exact superpose eq8282 eq702
    | (have j1 := eq8282 X0
       grind)
    | exact resolve eq702 eq8282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8282
  have eq8572 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq8562 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8562
    | (have j0 := eq8562 X0
       grind)
    | exact resolve eq8562 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8562
  have eq8675 : ∀ X0 X1 : G, (k X1 (M.op (σ x) (σ y))) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq735 X0
       have i₂ := eq8572 (M.op sF0 y)
       grind)
    | exact superpose eq8572 eq735
    | (have j1 := eq8572 X1
       grind)
    | exact resolve eq735 eq8572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8572
  have eq8974 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq794 X0
       have i₂ := eq8675 (k X0 X0) x
       grind)
    | exact superpose eq8675 eq794
    | (have j0 := eq794 (M.op (σ x) (σ y))
       have j1 := eq8675 X0 x
       grind)
    | (have r₁ := eq794 (M.op (σ x) (σ y))
       have r₂ := eq8675 X0 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq794 (M.op x y)
       have r₂ := eq8675 (M.op x y) x
       grind)
    | exact resolve eq794 eq8675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8675
  have eq8995 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq8974 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8974
  have eq9116 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2163 eq116
    | exact resolve eq116 eq2163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2163
  have eq9133 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq30 eq9116
    | exact resolve eq9116 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9116
  have eq9176 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq702 x x
       have i₂ := eq8995 (M.op x x)
       grind)
    | exact superpose eq8995 eq702
    | (have j1 := eq8995 X0
       grind)
    | exact resolve eq702 eq8995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9188 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq2363 eq9176
    | (have j0 := eq9176 X0
       have j1 := eq2363 X0
       grind)
    | exact resolve eq9176 eq2363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2363 eq9176
  have eq9205 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq8995 eq9188
    | (have j0 := eq9188 X0
       have j1 := eq8995 X0
       grind)
    | exact resolve eq9188 eq8995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8995 eq9188
  have eq9883 : (M.op (σ x) (σ x)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq9133 eq702
    | exact resolve eq702 eq9133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9888 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq2152 eq9883
    | exact resolve eq9883 eq2152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9883
  have eq9907 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq9133 eq9888
    | exact resolve eq9888 eq9133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9133 eq9888
  have eq9908 : x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9907
  have eq9927 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq9908
       grind)
    | exact superpose eq9908 eq41
    | exact resolve eq41 eq9908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq9931 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq841 y y
       have i₂ := eq9908
       grind)
    | exact superpose eq9908 eq841
    | (have j0 := eq841 y y
       grind)
    | exact resolve eq841 eq9908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9935 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9931
  have eq9936 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9935
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9935
    | exact resolve eq9935 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9935
  have eq9937 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9927
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9927
    | exact resolve eq9927 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9927
  have eq9943 : y = (M.op y y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2152 eq9936
    | exact resolve eq9936 eq2152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9936
  have eq9944 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9937
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9937
    | exact resolve eq9937 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9937
  have eq9978 : ∀ X0 : G, y ≠ X0 ∨ y = (k y X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq9943
       grind)
    | exact superpose eq9943 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq9943
       grind)
    | exact resolve eq13 eq9943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9995 : y ≠ y ∨ y = (k y y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq9943
       grind)
    | exact superpose eq9943 eq28
    | (have j0 := eq28 y y
       grind)
    | (have r₁ := eq28 y y
       have r₂ := eq9943
       grind)
    | (have r₁ := eq28 (σ y) (σ x)
       have r₂ := eq9943
       grind)
    | exact resolve eq28 eq9943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10000 : (M.op y y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq702 y y
       have i₂ := eq9943
       grind)
    | exact superpose eq9943 eq702
    | exact resolve eq702 eq9943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10001 : y = (k y y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9995
  have eq10009 : y = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9943 eq10000
    | exact resolve eq10000 eq9943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10000
  have eq10014 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9908 eq10001
    | exact resolve eq10001 eq9908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10001
  have eq10043 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10014 eq27
    | exact resolve eq27 eq10014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10107 : (σ y) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq3112 eq10043
    | (have r₁ := eq10043
       have r₂ := eq3112
       grind)
    | exact resolve eq10043 eq3112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10043
  have eq10108 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq10107
  have eq10109 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq3179 eq10108
    | exact resolve eq10108 eq3179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10108
  have eq10110 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq10109
  have eq10155 : ∀ X0 : G, y = (M.op y X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq10009 eq719
    | exact resolve eq719 eq10009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10207 : y = (k y (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10009 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq10009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10009
  have eq10234 : y = (k y (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq9978 (M.op x y)
       grind)
    | (have r₁ := eq10207
       have r₂ := eq9978 (k y (M.op x y))
       grind)
    | (have r₁ := eq10207
       have r₂ := eq9978 (M.op x y)
       grind)
    | exact resolve eq10207 eq9978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9978 eq10207
  have eq10280 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq10014 eq10155
    | exact resolve eq10155 eq10014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10014 eq10155
  have eq10291 : y = (k y (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10234
       have r₂ := eq2338
       grind)
    | exact resolve eq10234 eq2338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2338 eq10234
  have eq10319 : y = (k y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 y (M.op x y)
       grind)
    | (have r₁ := eq10291
       have r₂ := eq13 y (M.op x y)
       grind)
    | exact resolve eq10291 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10291
  have eq10327 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10319 eq42
    | exact resolve eq42 eq10319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10319
  have eq10332 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10327
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10327
    | exact resolve eq10327 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10327
  have eq10344 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq3112 eq10332
    | exact resolve eq10332 eq3112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3112
  have eq10348 : (M.op (σ y) (σ y)) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10332 eq841
    | (have j0 := eq841 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq841 eq10332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841 eq10332
  have eq10351 : (M.op (σ y) (σ y)) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4443 eq10348
    | exact resolve eq10348 eq4443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4443 eq10348
  have eq10355 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq9944 eq10344
    | exact resolve eq10344 eq9944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10344
  have eq10356 : (σ x) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2073 eq10351
    | exact resolve eq10351 eq2073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2073 eq10351
  have eq10358 : (σ x) = (σ y) ∨ (M.op x y) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq10110 eq10355
    | exact resolve eq10355 eq10110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10110 eq10355
  have eq10359 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2152 eq10356
    | exact resolve eq10356 eq2152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10356
  have eq10360 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10359
  have eq10361 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have r₁ := eq10358
       have r₂ := eq3166
       grind)
    | exact resolve eq10358 eq3166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3166 eq10358
  have eq10642 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq10280 y
       grind)
    | exact superpose eq10280 eq18
    | (have j1 := eq10280 y
       grind)
    | exact resolve eq18 eq10280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10280
  have eq10760 : (σ x) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10642
  have eq11199 : (M.op (M.op x y) y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10360 eq702
    | exact resolve eq702 eq10360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11204 : (σ (M.op x y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10360 eq11199
    | exact resolve eq11199 eq10360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10360 eq11199
  have eq11883 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11204 eq2152
    | exact resolve eq2152 eq11204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11204
  have eq11905 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq11883
  have eq11919 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq11905
       have r₂ := eq27
       grind)
    | exact resolve eq11905 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11905
  have eq11954 : (M.op (σ y) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq11919 eq708
    | exact resolve eq708 eq11919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12160 : (σ x) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq11954 eq1936
    | exact resolve eq1936 eq11954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1936
  have eq12166 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op x y) y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq11954 eq693
    | exact resolve eq693 eq11954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq12192 : (σ x) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq12160
  have eq12209 : (σ x) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2060 eq12192
    | exact resolve eq12192 eq2060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12192
  have eq12215 : (σ x) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2072 eq12209
    | exact resolve eq12209 eq2072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12209
  have eq15319 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2035 eq12166
    | exact resolve eq12166 eq2035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12166
  have eq15348 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq15319
  have eq15364 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq11919 eq15348
    | exact resolve eq15348 eq11919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15348
  have eq15369 : (σ y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq11954 eq15364
    | exact resolve eq15364 eq11954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11954 eq15364
  have eq15370 : (σ y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2060 eq15369
    | exact resolve eq15369 eq2060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2060 eq15369
  have eq15371 : (σ y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2072 eq15370
    | exact resolve eq15370 eq2072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2072 eq15370
  have eq15372 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq12215 eq15371
    | exact resolve eq15371 eq12215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12215 eq15371
  have eq15373 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq15372
  have eq15426 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq702 y y
       have i₂ := eq15373
       grind)
    | exact superpose eq15373 eq702
    | exact resolve eq702 eq15373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15373
  have eq15438 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq15426
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15426
    | exact resolve eq15426 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15426
  have eq15489 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq15438 eq719
    | exact resolve eq719 eq15438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15531 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq15438 eq2035
    | exact resolve eq2035 eq15438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2035
  have eq15552 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq15531
  have eq15563 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq15552
       have r₂ := eq10760
       grind)
    | exact resolve eq15552 eq10760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10760 eq15552
  have eq16155 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq702 y y
       have i₂ := eq15563
       grind)
    | exact superpose eq15563 eq702
    | exact resolve eq702 eq15563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15563
  have eq16167 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16155
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16155
    | exact resolve eq16155 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16155
  have eq16202 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq16167 eq735
    | exact resolve eq735 eq16167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16167
  have eq18051 : ∀ X0 : G, (M.op x y) ≠ (M.op (σ x) (σ y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq28 X0 x
       have i₂ := eq9205 (M.op x X0)
       grind)
    | exact superpose eq9205 eq28
    | (have j0 := eq28 (M.op x y) (M.op x y)
       have j1 := eq9205 (M.op x y)
       grind)
    | (have r₁ := eq28 (σ y) (σ x)
       have r₂ := eq9205 X0
       grind)
    | (have r₁ := eq28 y x
       have r₂ := eq9205 X0
       grind)
    | exact resolve eq28 eq9205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9205
  have eq18100 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq18051 (M.op x y)
       have j1 := eq16202 (M.op x y)
       grind)
    | (have r₁ := eq18051 X0
       have r₂ := eq16202 X0
       grind)
    | exact resolve eq18051 eq16202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16202 eq18051
  have eq18258 : (M.op (M.op x y) y) = (M.op y x) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq806 y
       have i₂ := eq9908
       grind)
    | exact superpose eq9908 eq806
    | (have j0 := eq806 y
       grind)
    | exact resolve eq806 eq9908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq18323 : (M.op (σ x) (σ y)) = (M.op y x) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2152 eq18258
    | exact resolve eq18258 eq2152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18258
  have eq18353 : (M.op x y) = (M.op y x) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9943 eq18323
    | exact resolve eq18323 eq9943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18323
  have eq18764 : (M.op x y) ≠ (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j0 := eq18100 (M.op x y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18100
  have eq18765 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18764
  have eq18795 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18765 eq42
    | exact resolve eq42 eq18765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18802 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18765 eq792
    | (have j0 := eq792 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq792 (M.op x y) (M.op x y)
       have r₂ := eq18765
       grind)
    | exact resolve eq792 eq18765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18803 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18802
  have eq18804 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18803
  have eq18816 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq18795
    | exact resolve eq18795 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18795
  have eq18862 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18804 eq702
    | exact resolve eq702 eq18804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18887 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18804 eq18862
    | exact resolve eq18862 eq18804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18804 eq18862
  have eq18948 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18816 eq792
    | (have j0 := eq792 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq792 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq18816
       grind)
    | exact resolve eq792 eq18816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18816
  have eq18949 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18948
  have eq18950 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18949
  have eq18974 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18887 eq719
    | exact resolve eq719 eq18887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18975 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18887 eq735
    | exact resolve eq735 eq18887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq18984 : ∀ X0 : G, (k X0 (τ (M.op x y))) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18887 eq759
    | exact resolve eq759 eq18887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19100 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18950 eq702
    | exact resolve eq702 eq18950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19118 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18887 eq19100
    | exact resolve eq19100 eq18887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19100
  have eq19548 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19118 eq18950
    | exact resolve eq18950 eq19118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18950 eq19118
  have eq19583 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq19548
  have eq20087 : (τ (M.op x y)) ≠ (τ (M.op x y)) ∨ (τ (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18984 eq794
    | (have j0 := eq794 (τ (M.op x y))
       grind)
    | (have r₁ := eq794 (τ (M.op x y))
       have r₂ := eq18984 (τ (M.op x y))
       grind)
    | exact resolve eq794 eq18984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18984
  have eq20113 : (τ (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20087
  have eq22427 : (M.op (τ (M.op x y)) (τ (M.op x y))) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20113 eq702
    | exact resolve eq702 eq20113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22445 : (M.op x y) = (M.op (τ (M.op x y)) (τ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18887 eq22427
    | exact resolve eq22427 eq18887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22427
  have eq22487 : (M.op x y) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22445 eq20113
    | exact resolve eq20113 eq22445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20113 eq22445
  have eq22529 : (M.op x y) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22487
  have eq26295 : (M.op (M.op x y) y) = (M.op (M.op x y) x) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq702 y x
       have i₂ := eq18353
       grind)
    | exact superpose eq18353 eq702
    | exact resolve eq702 eq18353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18353
  have eq26298 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2152 eq26295
    | exact resolve eq26295 eq2152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26295
  have eq26305 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9943 eq26298
    | exact resolve eq26298 eq9943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9943 eq26298
  have eq27377 : (M.op x y) ≠ (M.op x y) ∨ x = (k x (M.op x y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26305 eq28
    | (have j0 := eq28 x (M.op x y)
       grind)
    | (have r₁ := eq28 x (M.op x y)
       have r₂ := eq26305
       grind)
    | (have r₁ := eq28 y y
       have r₂ := eq26305
       grind)
    | (have r₁ := eq28 (σ y) (σ x)
       have r₂ := eq26305
       grind)
    | exact resolve eq28 eq26305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26305
  have eq27384 : y = (M.op y y) ∨ x = (k x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq27377
  have eq27848 : (σ y) = (k (σ y) (σ y)) ∨ x = (k x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq182
       have i₂ := eq27384
       grind)
    | exact superpose eq27384 eq182
    | exact resolve eq182 eq27384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq27877 : y ≠ y ∨ y = (k y y) ∨ x = (k x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq27384
       grind)
    | exact superpose eq27384 eq28
    | (have j0 := eq28 y y
       grind)
    | (have r₁ := eq28 y y
       have r₂ := eq27384
       grind)
    | (have r₁ := eq28 (σ y) (σ x)
       have r₂ := eq27384
       grind)
    | exact resolve eq28 eq27384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq27384
  have eq27883 : y = (k y y) ∨ x = (k x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq27877
  have eq27904 : x = y ∨ x = (k x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9908 eq27883
    | exact resolve eq27883 eq9908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27883
  have eq27915 : (σ y) = (k (σ y) (σ y)) ∨ x = (k x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27848
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq27848
    | exact resolve eq27848 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq27848
  have eq27920 : x = (k x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18975 eq27904
    | (have j1 := eq18975 x
       grind)
    | exact resolve eq27904 eq18975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18975 eq27904
  have eq27927 : x = (k x (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9944 eq27915
    | exact resolve eq27915 eq9944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9944 eq27915
  have eq27934 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27920 eq42
    | exact resolve eq42 eq27920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27920
  have eq27940 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27934
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27934
    | exact resolve eq27934 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27934
  have eq27944 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11919 eq27940
    | exact resolve eq27940 eq11919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27940
  have eq27952 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27927 eq42
    | exact resolve eq42 eq27927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq27955 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27927 eq792
    | (have j0 := eq792 (M.op x y) x
       grind)
    | exact resolve eq792 eq27927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27927
  have eq27956 : (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq18974 x
       grind)
    | (have r₁ := eq27955
       have r₂ := eq18974 x
       grind)
    | exact resolve eq27955 eq18974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18974 eq27955
  have eq27958 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27952
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27952
    | exact resolve eq27952 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27952
  have eq27960 : (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15489 eq27956
    | (have j1 := eq15489 x
       grind)
    | exact resolve eq27956 eq15489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27956
  have eq27962 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11919 eq27958
    | exact resolve eq27958 eq11919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11919 eq27958
  have eq27964 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15489 eq27960
    | (have j1 := eq15489 (M.op x y)
       grind)
    | exact resolve eq27960 eq15489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15489 eq27960
  have eq27965 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq27964
  have eq27981 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27944 eq792
    | (have j0 := eq792 (σ x) (σ x)
       grind)
    | (have r₁ := eq792 (σ x) (σ x)
       have r₂ := eq27944
       grind)
    | exact resolve eq792 eq27944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27944
  have eq27982 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq27981
  have eq27983 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq27982
  have eq28147 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27962 eq142
    | exact resolve eq142 eq27962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq27962
  have eq28161 : x = (k x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq28147
    | exact resolve eq28147 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28147
  have eq28211 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27965 eq702
    | exact resolve eq702 eq27965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28228 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27965 eq28211
    | exact resolve eq28211 eq27965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27965 eq28211
  have eq28305 : (M.op (σ x) (σ x)) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27983 eq702
    | exact resolve eq702 eq27983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28318 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2152 eq28305
    | exact resolve eq28305 eq2152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2152 eq28305
  have eq28339 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27983 eq28318
    | exact resolve eq28318 eq27983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27983 eq28318
  have eq28340 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq28339
  have eq28374 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq29469 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq792 x x
       have i₂ := eq28161
       grind)
    | exact superpose eq28161 eq792
    | (have j0 := eq792 x x
       grind)
    | (have r₁ := eq792 x x
       have r₂ := eq28161
       grind)
    | exact resolve eq792 eq28161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792 eq28161
  have eq29470 : x ≠ x ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq29469
  have eq29471 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq29470
  have eq29826 : (M.op x x) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq702 x x
       have i₂ := eq29471
       grind)
    | exact superpose eq29471 eq702
    | exact resolve eq702 eq29471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29837 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28228 eq29826
    | exact resolve eq29826 eq28228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28228 eq29826
  have eq30390 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29471
       have i₂ := eq29837
       grind)
    | exact superpose eq29837 eq29471
    | exact resolve eq29471 eq29837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29471 eq29837
  have eq30429 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq30390
  have eq30486 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30429 eq27
    | exact resolve eq27 eq30429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30489 : (M.op (σ y) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30429 eq708
    | exact resolve eq708 eq30429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30429
  have eq30532 : (M.op x y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15438 eq30489
    | exact resolve eq30489 eq15438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15438 eq30489
  have eq30533 : (M.op x y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10361 eq30486
    | exact resolve eq30486 eq10361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10361 eq30486
  have eq30575 : (M.op x y) = (k (σ y) (σ y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30532 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq30532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30532
  have eq30583 : (M.op x y) = (k (σ y) (σ y)) ∨ (M.op x y) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq30575
  have eq30619 : (M.op x y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq30583
       have r₂ := eq30533
       grind)
    | exact resolve eq30583 eq30533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30533 eq30583
  have eq30658 : (k y y) = (τ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30619 eq116
    | exact resolve eq116 eq30619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30619
  have eq30716 : (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22529 eq30658
    | exact resolve eq30658 eq22529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30658
  have eq30765 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2190
       have i₂ := eq30716
       grind)
    | exact superpose eq30716 eq2190
    | exact resolve eq2190 eq30716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2190 eq30716
  have eq30792 : x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq30765
  have eq30816 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq30792
       have r₂ := eq28374
       grind)
    | exact resolve eq30792 eq28374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28374 eq30792
  have eq30854 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30816 eq27
    | exact resolve eq27 eq30816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30857 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30816 eq708
    | exact resolve eq708 eq30816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30879 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq30857
    | exact resolve eq30857 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30857
  have eq30881 : (M.op x y) ≠ (σ x) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3179 eq30854
    | exact resolve eq30854 eq3179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30854
  have eq30896 : (σ x) = (M.op (M.op x y) y) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30816 eq30879
    | exact resolve eq30879 eq30816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30816 eq30879
  have eq30902 : (M.op x y) = (σ x) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2192 eq30896
    | exact resolve eq30896 eq2192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2192 eq30896
  have eq30903 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq30902
       have r₂ := eq30881
       grind)
    | exact resolve eq30902 eq30881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30881 eq30902
  have eq30982 : x = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9908
       have i₂ := eq30903
       grind)
    | exact superpose eq30903 eq9908
    | exact resolve eq9908 eq30903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9908 eq30903
  have eq31036 : x = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28340 eq30982
    | exact resolve eq30982 eq28340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28340 eq30982
  have eq31037 : x = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq31036
  have eq31064 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18765 eq31037
    | exact resolve eq31037 eq18765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18765 eq31037
  have eq31065 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq31064
  have eq31218 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31065 eq27
    | exact resolve eq27 eq31065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31221 : (M.op (σ y) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31065 eq708
    | exact resolve eq708 eq31065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31065
  have eq31271 : (M.op x y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18887 eq31221
    | exact resolve eq31221 eq18887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31221
  have eq31272 : (M.op x y) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19583 eq31218
    | exact resolve eq31218 eq19583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31218
  have eq31368 : (M.op x y) = (k (σ y) (σ y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31271 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq31271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31271
  have eq31376 : (M.op x y) = (k (σ y) (σ y)) ∨ (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq31368
  have eq31413 : (M.op x y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq31376
       have r₂ := eq31272
       grind)
    | exact resolve eq31376 eq31272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31376
  have eq31453 : (k y y) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31413 eq116
    | exact resolve eq116 eq31413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq31413
  have eq31506 : (M.op x y) = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22529 eq31453
    | exact resolve eq31453 eq22529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22529 eq31453
  have eq31551 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2123
       have i₂ := eq31506
       grind)
    | exact superpose eq31506 eq2123
    | exact resolve eq2123 eq31506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2123 eq31506
  have eq31580 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq31551
  have eq31598 : x = (M.op x y) ∨ (M.op x y) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19583 eq31580
    | exact resolve eq31580 eq19583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19583 eq31580
  have eq31604 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq31598
       have r₂ := eq31272
       grind)
    | exact resolve eq31598 eq31272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31272 eq31598
  have eq33204 : (M.op x x) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq702 x x
       have i₂ := eq31604
       grind)
    | exact superpose eq31604 eq702
    | exact resolve eq702 eq31604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33225 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18887 eq33204
    | exact resolve eq33204 eq18887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18887 eq33204
  have eq33333 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31604
       have i₂ := eq33225
       grind)
    | exact superpose eq33225 eq31604
    | exact resolve eq31604 eq33225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31604 eq33225
  have eq33379 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq33333
  have eq33431 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33379 eq27
    | exact resolve eq27 eq33379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33433 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq33379 eq700
    | exact resolve eq700 eq33379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq33434 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33379 eq708
    | exact resolve eq708 eq33379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq33454 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq33434
    | exact resolve eq33434 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33434
  have eq33455 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq33433
    | (have j0 := eq33433 X0
       grind)
    | exact resolve eq33433 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33433
  have eq33459 : (σ x) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33379 eq33454
    | exact resolve eq33454 eq33379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33454
  have eq33460 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq33379 eq33455
    | exact resolve eq33455 eq33379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33379 eq33455
  have eq33464 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3179 eq33431
    | exact resolve eq33431 eq3179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3179 eq33431
  have eq33467 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq33464
  have eq33509 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq33459 eq759
    | exact resolve eq759 eq33459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq33559 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33459 eq2362
    | exact resolve eq2362 eq33459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2362
  have eq33581 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq33559
  have eq33620 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq33581
       have r₂ := eq33467
       grind)
    | exact resolve eq33581 eq33467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33467 eq33581
  have eq33639 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30 eq33509
    | exact resolve eq33509 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq33509
  have eq33659 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq33620
       grind)
    | exact superpose eq33620 eq18
    | exact resolve eq18 eq33620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33620
  have eq34192 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq794 x
       have i₂ := eq33639 x
       grind)
    | exact superpose eq33639 eq794
    | (have j0 := eq794 x
       grind)
    | (have r₁ := eq794 x
       have r₂ := eq33639 x
       grind)
    | exact resolve eq794 eq33639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794 eq33639
  have eq34232 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq34192
  have eq34499 : (M.op x x) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq702 x x
       have i₂ := eq34232
       grind)
    | exact superpose eq34232 eq702
    | exact resolve eq702 eq34232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34519 : (σ x) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33459 eq34499
    | exact resolve eq34499 eq33459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33459 eq34499
  have eq34648 : x = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq34232
       have i₂ := eq34519
       grind)
    | exact superpose eq34519 eq34232
    | exact resolve eq34232 eq34519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34232 eq34519
  have eq34690 : x = (σ x) ∨ x = (M.op x y) := by grind
  clear eq34648
  have eq34796 : (M.op x y) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq33659
       have i₂ := eq34690
       grind)
    | exact superpose eq34690 eq33659
    | exact resolve eq33659 eq34690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33659
  have eq34799 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) := by grind
  clear eq34690
  have eq34801 : (M.op x y) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq34796
       have r₂ := eq34799
       grind)
    | exact resolve eq34796 eq34799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34796
  have eq35001 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq34801 eq33460
    | exact resolve eq33460 eq34801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33460 eq34801
  have eq35017 : (M.op x y) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq35001
  have eq35033 : x = (M.op x y) := by
    first
    | (have r₁ := eq35017
       have r₂ := eq34799
       grind)
    | exact resolve eq35017 eq34799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34799 eq35017
  have eq35047 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq35033
       grind)
    | exact superpose eq35033 eq18
    | exact resolve eq18 eq35033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq35048 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq35033
       grind)
    | exact superpose eq35033 eq22
    | exact resolve eq22 eq35033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35033
  have eq35087 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq35048 eq20
    | exact resolve eq20 eq35048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35048
  have eq35295 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq35047 eq719
    | exact resolve eq719 eq35047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq35304 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq35047 eq758
    | exact resolve eq758 eq35047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq35372 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq35304
    | (have j0 := eq35304 X0
       grind)
    | exact resolve eq35304 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq35304
  have eq35393 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq35087 eq35372
    | exact resolve eq35372 eq35087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35372
  have eq35522 : (σ x) ≠ (σ (k x x)) ∨ (σ (k x x)) = (M.op (σ (k x x)) (σ x)) ∨ (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1954 x (k x x)
       have i₂ := eq811
       grind)
    | exact superpose eq811 eq1954
    | (have j0 := eq1954 x x
       grind)
    | exact resolve eq1954 eq811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811 eq1954
  have eq35805 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ (k x x)) = (M.op (σ (k x x)) (σ x)) ∨ (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq35522
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq35522
    | exact resolve eq35522 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35522
  have eq35889 : (σ (k x x)) = (M.op (σ (k x x)) (σ x)) ∨ (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq35805
       have r₂ := eq35393 (σ x)
       grind)
    | exact resolve eq35805 eq35393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35805
  have eq35961 : (σ (k x x)) = (M.op (σ (k x x)) (σ x)) ∨ (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq35889
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35889
    | exact resolve eq35889 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35889
  have eq36024 : (k (σ x) (σ x)) = (M.op (k (σ x) (σ x)) (σ x)) ∨ (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq35961
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq35961
    | exact resolve eq35961 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35961
  have eq36080 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq35393 eq36024
    | exact resolve eq36024 eq35393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36024
  have eq36127 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq36080
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36080
    | exact resolve eq36080 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36080
  have eq36128 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq36127
  have eq36170 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq36128
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36128
    | exact resolve eq36128 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36128
  have eq36200 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq36170
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq36170
    | exact resolve eq36170 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq36170
  have eq36228 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq35393 eq36200
    | exact resolve eq36200 eq35393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35393 eq36200
  have eq36247 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq36228
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36228
    | exact resolve eq36228 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq36228
  have eq36248 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq36247
  have eq36784 : (M.op (σ x) (σ x)) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq36248 eq702
    | exact resolve eq702 eq36248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq36787 : (M.op x y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq35047 eq36784
    | exact resolve eq36784 eq35047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35047 eq36784
  have eq36828 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq36787 eq36248
    | exact resolve eq36248 eq36787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36248 eq36787
  have eq36892 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq36828 eq26
    | exact resolve eq26 eq36828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq37033 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35295 eq36892
    | exact resolve eq36892 eq35295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35295 eq36892
  have eq37083 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq37033 eq27
    | exact resolve eq27 eq37033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq37033
  have eq37144 : (M.op x y) ≠ (σ x) := by
    first
    | exact superpose eq35087 eq37083
    | exact resolve eq37083 eq35087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35087 eq37083
  have eq37148 : False := by grind
  exact eq37148

/-- `Equation4393`: `x ◇ (x ◇ x) = (y ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation4393 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4393 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4393.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X2) := by
    intro X0 X1 X2
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq13 X0 (k (M.op X0 X0) X1)
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y
       grind)
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq45
    | exact resolve eq45 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq175 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : (σ x) = (k (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq36 (M.op x x)
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq36
    | exact resolve eq36 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq178 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq38 (M.op sF0 sF0)
       have i₂ := eq175 sF0
       grind)
    | exact superpose eq175 eq38
    | exact resolve eq38 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq179 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq20 eq178
    | exact resolve eq178 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq181 : (σ x) = (k (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq176
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq176
    | exact resolve eq176 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq189 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq91 (M.op sF2 sF2)
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq91
    | exact resolve eq91 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq200 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq30 eq189
    | exact resolve eq189 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq207 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq108 (M.op sF3 sF3)
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq108
    | exact resolve eq108 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq218 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq32 eq207
    | exact resolve eq207 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq207
  have eq397 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq688 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X3 X4) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq16 x X3 X4
       have i₂ := eq16 x X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq690 : ∀ X0 X1 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X0 (M.op X0 X0)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X1 (M.op x X3) X3
       have i₂ := eq16 X0 x X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq692 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq694 : ∀ X1 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X3) := by
    intro X1 X3
    first
    | (have i₁ := eq690 x X1 X3
       have i₂ := eq692 x
       grind)
    | exact superpose eq692 eq690
    | exact resolve eq690 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq696 : ∀ X3 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X3) := by
    intro X3
    first
    | (have i₁ := eq694 x X3
       have i₂ := eq692 x
       grind)
    | exact superpose eq692 eq694
    | exact resolve eq694 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq698 : ∀ X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op (M.op x y) y) := by
    intro X1 X2
    first
    | (have i₁ := eq16 x X1 X2
       have i₂ := eq691 x
       grind)
    | exact superpose eq691 eq16
    | exact resolve eq16 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (M.op x y) y) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op X1 X1)
       have i₂ := eq691 X1
       grind)
    | exact superpose eq691 eq16
    | exact resolve eq16 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq700 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op x y) y) (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq699 x X1
       have i₂ := eq692 x
       grind)
    | exact superpose eq692 eq699
    | exact resolve eq699 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq703 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq691 x
       have i₂ := eq692 x
       grind)
    | exact superpose eq692 eq691
    | exact resolve eq691 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq712 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq703 eq696
    | exact resolve eq696 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq721 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq696 eq28
    | (have j0 := eq28 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | (have r₁ := eq28 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq696 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact resolve eq28 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq726 : ∀ X0 : G, (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq721 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq730 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | exact superpose eq703 eq726
    | exact resolve eq726 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq738 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq730 eq35
    | exact resolve eq35 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq751 : ∀ X0 : G, (k X0 (σ (M.op (M.op x y) y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq738 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq738
    | exact resolve eq738 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq777 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq28
    | (have j0 := eq28 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq28 X0 (M.op X0 X0)
       have r₂ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq782 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X2)) = (M.op (k X0 X1) X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X1 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq787 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq795 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq801 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq802 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq801 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq813 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq777 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq829 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (k X0 X1) X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq782 X0 X1 x
       have i₂ := eq692 x
       grind)
    | exact superpose eq692 eq782
    | (have j0 := eq782 X1 X1 x
       grind)
    | exact resolve eq782 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692 eq782
  have eq832 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq813 X0 X1
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq813 X1 X1
       have r₂ := eq28 X1 X1
       grind)
    | (have r₁ := eq813 X1 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq813 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813
  have eq846 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op (k X0 X1) X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq703 eq829
    | (have j0 := eq829 X1 X1
       grind)
    | exact resolve eq829 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq849 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq802 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq802
    | (have j0 := eq802 (σ X0)
       grind)
    | exact resolve eq802 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq864 : (σ (M.op (M.op x y) y)) ≠ (σ (M.op (M.op x y) y)) ∨ (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq751 eq802
    | (have j0 := eq802 (σ (M.op (M.op x y) y))
       grind)
    | (have r₁ := eq802 (σ (M.op (M.op x y) y))
       have r₂ := eq751 (σ (M.op (M.op x y) y))
       grind)
    | exact resolve eq802 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq877 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by grind
  clear eq864
  have eq1535 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq787
       grind)
    | exact superpose eq787 eq40
    | exact resolve eq40 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1536 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1535
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1535
    | exact resolve eq1535 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535
  have eq1538 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1536
    | exact resolve eq1536 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1536
  have eq18915 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    intro X0 X1
    first
    | exact superpose eq877 eq688
    | exact resolve eq688 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18921 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (σ (M.op (M.op x y) y)) := by
    intro X0 X1
    first
    | exact superpose eq877 eq18915
    | exact resolve eq18915 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877 eq18915
  have eq18934 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq18921 x x
       have i₂ := eq698 x x
       grind)
    | (have i₁ := eq18921 x y
       have i₂ := eq698 x x
       grind)
    | exact superpose eq698 eq18921
    | (have j0 := eq18921 x y
       grind)
    | exact resolve eq18921 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18921
  have eq18973 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq18934 eq15
    | exact resolve eq15 eq18934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21815 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1538 eq795
    | exact resolve eq795 eq1538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21823 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq21815
       have r₂ := eq27
       grind)
    | exact resolve eq21815 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21815
  have eq21830 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21823 eq218
    | exact resolve eq218 eq21823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq21823
  have eq21861 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq21830
    | exact resolve eq21830 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21830
  have eq21871 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq21861
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq21861
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq21861
       have r₂ := eq13 y x
       grind)
    | exact resolve eq21861 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21861
  have eq21874 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) := by
    first
    | (have j1 := eq28 y x
       grind)
    | (have r₁ := eq21871
       have r₂ := eq28 x (σ x)
       grind)
    | (have r₁ := eq21871
       have r₂ := eq28 x x
       grind)
    | exact resolve eq21871 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21871
  have eq21876 : x = (k x (τ (σ x))) ∨ y = (k y x) := by
    first
    | exact superpose eq21874 eq200
    | exact resolve eq200 eq21874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq21874
  have eq21906 : x = (k x x) ∨ y = (k y x) := by
    first
    | exact superpose eq30 eq21876
    | exact resolve eq21876 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21876
  have eq21915 : y = (k y x) := by
    first
    | (have j1 := eq832 x y
       grind)
    | (have r₁ := eq21906
       have r₂ := eq832 x x
       grind)
    | exact resolve eq21906 eq832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832 eq21906
  have eq21923 : x = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq787
       have i₂ := eq21915
       grind)
    | exact superpose eq21915 eq787
    | exact resolve eq787 eq21915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq21925 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq21915
       grind)
    | exact superpose eq21915 eq40
    | exact resolve eq40 eq21915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq21915
  have eq21927 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq21925
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21925
    | exact resolve eq21925 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21925
  have eq21934 : x = (M.op y y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21927 eq1538
    | exact resolve eq1538 eq21927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538
  have eq21937 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21927 eq795
    | exact resolve eq795 eq21927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795 eq21927
  have eq22433 : x = (k y y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq21923
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq21923
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq21923 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22445 : x = (k y y) ∨ x = y ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq21923
       grind)
    | exact superpose eq21923 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq21923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22450 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq698 y y
       have i₂ := eq21923
       grind)
    | exact superpose eq21923 eq698
    | exact resolve eq698 eq21923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21923
  have eq22451 : x = (k y y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq22445
  have eq22452 : x = (k y y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq22433
  have eq22453 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq22450
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22450
    | exact resolve eq22450 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22450
  have eq22465 : x = (k y y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq22451 eq22452
    | exact resolve eq22452 eq22451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22451 eq22452
  have eq22466 : x = (k y y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq22465
  have eq22493 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq698 y y
       have i₂ := eq21934
       grind)
    | exact superpose eq21934 eq698
    | exact resolve eq698 eq21934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21934
  have eq22496 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq22493
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22493
    | exact resolve eq22493 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22493
  have eq22519 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq21937
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq21937
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq21937 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22531 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21937 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq21937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22536 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21937 eq698
    | exact resolve eq698 eq21937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21937
  have eq22537 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22531
  have eq22538 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq22519
  have eq22539 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq22536
    | exact resolve eq22536 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22536
  have eq22551 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq22537 eq22538
    | exact resolve eq22538 eq22537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22537 eq22538
  have eq22552 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22551
  have eq22567 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22453 eq730
    | exact resolve eq730 eq22453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22623 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22453 eq18934
    | exact resolve eq18934 eq22453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22453
  have eq22638 : x = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq22623
    | exact resolve eq22623 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22623
  have eq22924 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq28 X0 x
       have i₂ := eq22638
       grind)
    | exact superpose eq22638 eq28
    | (have j0 := eq28 X0 x
       grind)
    | (have r₁ := eq28 X0 x
       have r₂ := eq22638
       grind)
    | exact resolve eq28 eq22638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22937 : (M.op x x) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq698 x x
       have i₂ := eq22638
       grind)
    | exact superpose eq22638 eq698
    | exact resolve eq698 eq22638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22938 : ∀ X0 : G, (k X0 x) = X0 ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq22924 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22924
  have eq22940 : x = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22638 eq22937
    | exact resolve eq22937 eq22638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22638 eq22937
  have eq23211 : x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22940 eq18934
    | exact resolve eq18934 eq22940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23222 : x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22940 eq698
    | exact resolve eq698 eq22940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22940
  have eq23226 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq23222
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23222
    | exact resolve eq23222 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23222
  have eq23232 : x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq23211
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23211
    | exact resolve eq23211 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23211
  have eq23289 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23226 eq23232
    | exact resolve eq23232 eq23226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23232
  have eq23449 : x = (τ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23289 eq30
    | exact resolve eq30 eq23289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23455 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23289 eq60
    | exact resolve eq60 eq23289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq23560 : ∀ X0 : G, (k X0 x) = (k X0 (τ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq23455 X0
       have i₂ := eq397 X0 sF0
       grind)
    | exact superpose eq397 eq23455
    | exact resolve eq23455 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397 eq23455
  have eq23566 : (M.op x y) = (τ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23226 eq23449
    | exact resolve eq23449 eq23226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23226 eq23449
  have eq23603 : ∀ X0 : G, (k X0 (τ (M.op x y))) = X0 ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22938 eq23560
    | exact resolve eq23560 eq22938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22938 eq23560
  have eq23628 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23566 eq23603
    | exact resolve eq23603 eq23566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23603
  have eq23810 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23566 eq14
    | exact resolve eq14 eq23566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23566
  have eq23874 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq23810
    | exact resolve eq23810 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23810
  have eq23875 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq23874
  have eq23895 : (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23875 eq29
    | exact resolve eq29 eq23875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq25573 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq22466
       grind)
    | exact superpose eq22466 eq41
    | exact resolve eq41 eq22466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22466
  have eq25590 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25573
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25573
    | exact resolve eq25573 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25573
  have eq25597 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25590
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25590
    | exact resolve eq25590 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25590
  have eq25608 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq22496 eq730
    | exact resolve eq730 eq22496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25664 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq22496 eq18934
    | exact resolve eq18934 eq22496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22496
  have eq25682 : x = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq25664
    | exact resolve eq25664 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25664
  have eq25972 : x = (k x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq175 x
       have i₂ := eq25682
       grind)
    | exact superpose eq25682 eq175
    | exact resolve eq175 eq25682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25984 : (M.op x x) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq698 x x
       have i₂ := eq25682
       grind)
    | exact superpose eq25682 eq698
    | exact resolve eq698 eq25682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25987 : (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq23875 eq25984
    | exact resolve eq25984 eq23875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25984
  have eq26000 : x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq25682 eq25987
    | exact resolve eq25987 eq25682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25682 eq25987
  have eq26031 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq849 x
       have i₂ := eq25972
       grind)
    | exact superpose eq25972 eq849
    | (have j0 := eq849 x
       grind)
    | exact resolve eq849 eq25972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25972
  have eq26039 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq26031
  have eq26044 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq26039
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26039
    | exact resolve eq26039 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26039
  have eq26504 : (M.op (σ x) (σ x)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26044 eq698
    | exact resolve eq698 eq26044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26508 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq23875 eq26504
    | exact resolve eq26504 eq23875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23875 eq26504
  have eq26521 : x = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26000 eq26508
    | exact resolve eq26508 eq26000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26000 eq26508
  have eq26531 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq26044 eq26521
    | exact resolve eq26521 eq26044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26044 eq26521
  have eq26612 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by grind
  have eq28745 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq22539 eq730
    | exact resolve eq730 eq22539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq28801 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22539 eq18934
    | exact resolve eq18934 eq22539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29036 : (M.op (σ x) (σ x)) = (M.op (M.op x y) y) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28801 eq698
    | exact resolve eq698 eq28801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29039 : (σ x) = (M.op (M.op x y) y) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28801 eq29036
    | exact resolve eq29036 eq28801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28801 eq29036
  have eq29397 : (σ x) = (τ (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29039 eq18973
    | exact resolve eq18973 eq29039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29039
  have eq29420 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq29397
    | exact resolve eq29397 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29397
  have eq31845 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22552 eq116
    | exact resolve eq116 eq22552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq22552
  have eq31869 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq31845
    | exact resolve eq31845 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31845
  have eq32336 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq181
       have i₂ := eq22567 X0
       grind)
    | exact superpose eq22567 eq181
    | (have j1 := eq22567 X0
       grind)
    | exact resolve eq181 eq22567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq32351 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) y) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq698 x x
       have i₂ := eq22567 X0
       grind)
    | exact superpose eq22567 eq698
    | (have j1 := eq22567 X0
       grind)
    | exact resolve eq698 eq22567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32354 : ∀ X0 : G, x = (M.op (M.op x y) y) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22567 eq32351
    | (have j0 := eq32351 X0
       have j1 := eq22567 X0
       grind)
    | exact resolve eq32351 eq22567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22567 eq32351
  have eq32366 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq32336 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32336
    | (have j0 := eq32336 X0
       grind)
    | exact resolve eq32336 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32336
  have eq32958 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) y) ∨ (k X0 (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq698 x x
       have i₂ := eq25608 X0
       grind)
    | exact superpose eq25608 eq698
    | (have j1 := eq25608 X0
       grind)
    | exact resolve eq698 eq25608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32961 : ∀ X0 : G, x = (M.op (M.op x y) y) ∨ (k X0 (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq25608 eq32958
    | (have j0 := eq32958 X0
       have j1 := eq25608 X0
       grind)
    | exact resolve eq32958 eq25608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25608 eq32958
  have eq33068 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op x y) y) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq698 x x
       have i₂ := eq28745 (M.op x x)
       grind)
    | exact superpose eq28745 eq698
    | (have j1 := eq28745 X0
       grind)
    | exact resolve eq698 eq28745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33071 : ∀ X0 : G, (σ x) = (M.op (M.op x y) y) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq28745 eq33068
    | (have j0 := eq33068 X0
       have j1 := eq28745 X0
       grind)
    | exact resolve eq33068 eq28745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28745 eq33068
  have eq33122 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq31869 eq28
    | (have j0 := eq28 X0 (σ x)
       grind)
    | (have r₁ := eq28 X0 (σ x)
       have r₂ := eq31869
       grind)
    | exact resolve eq28 eq31869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33136 : (M.op (σ x) (σ x)) = (M.op (M.op x y) y) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31869 eq698
    | exact resolve eq698 eq31869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33137 : ∀ X0 : G, x = (k y y) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq33122 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33122
  have eq33139 : (σ x) = (M.op (M.op x y) y) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31869 eq33136
    | exact resolve eq33136 eq31869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31869 eq33136
  have eq33493 : ∀ X0 : G, x = (σ x) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18934
       have i₂ := eq32354 (M.op sF0 y)
       grind)
    | exact superpose eq32354 eq18934
    | (have j1 := eq32354 X0
       grind)
    | exact resolve eq18934 eq32354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18934
  have eq33511 : ∀ X0 : G, x = (M.op x y) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq698 x x
       have i₂ := eq32354 (M.op x x)
       grind)
    | exact superpose eq32354 eq698
    | (have j1 := eq32354 X0
       grind)
    | exact resolve eq698 eq32354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32354
  have eq33522 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq33511 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq33511
    | (have j0 := eq33511 X0
       grind)
    | exact resolve eq33511 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33511
  have eq33529 : ∀ X0 : G, x = (σ x) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq33493 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq33493
    | (have j0 := eq33493 X0
       grind)
    | exact resolve eq33493 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33493
  have eq33588 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq33522 eq33529
    | (have j0 := eq33529 X0
       have j1 := eq33522 X0
       grind)
    | exact resolve eq33529 eq33522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33522 eq33529
  have eq33866 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33588 eq802
    | (have j0 := eq802 (M.op x y)
       grind)
    | (have r₁ := eq802 (M.op x y)
       have r₂ := eq33588 (M.op x y)
       grind)
    | exact resolve eq802 eq33588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33937 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq33866
  have eq34185 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33937 eq698
    | exact resolve eq698 eq33937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34193 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33937 eq34185
    | exact resolve eq34185 eq33937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33937 eq34185
  have eq36177 : ∀ X0 : G, (σ (σ x)) ≠ (σ (σ x)) ∨ (σ (σ x)) = (M.op (σ (σ x)) (σ (σ x))) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq849 X0
       have i₂ := eq32366 (k X0 X0)
       grind)
    | exact superpose eq32366 eq849
    | (have j0 := eq849 (σ x)
       have j1 := eq32366 X0
       grind)
    | exact resolve eq849 eq32366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32366
  have eq36189 : ∀ X0 : G, (σ (σ x)) = (M.op (σ (σ x)) (σ (σ x))) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq36177 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36177
  have eq36196 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq33588 eq36189
    | (have j0 := eq36189 X0
       have j1 := eq33588 X0
       grind)
    | exact resolve eq36189 eq33588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33588 eq36189
  have eq36204 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq36196
    | (have j0 := eq36196 X0
       grind)
    | exact resolve eq36196 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36196
  have eq36207 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23628 eq36204
    | (have j0 := eq36204 X0
       have j1 := eq23628 X0
       grind)
    | exact resolve eq36204 eq23628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23628 eq36204
  have eq36210 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq36207 X0
       have j1 := eq28 X0 (M.op x y)
       grind)
    | (have r₁ := eq36207 X0
       have r₂ := eq28 X0 (M.op x y)
       grind)
    | exact resolve eq36207 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36207
  have eq36217 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36210 eq802
    | (have j0 := eq802 (M.op x y)
       grind)
    | (have r₁ := eq802 (M.op x y)
       have r₂ := eq36210 (M.op x y)
       grind)
    | exact resolve eq802 eq36210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36288 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq36217
  have eq36534 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36288 eq698
    | exact resolve eq698 eq36288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36542 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36288 eq36534
    | exact resolve eq36534 eq36288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36288 eq36534
  have eq36587 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq36542 eq712
    | exact resolve eq712 eq36542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38187 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op X0 X1) X1) ∨ (k X2 (M.op x y)) = X2 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq688 X0 X1 x x
       have i₂ := eq32961 (M.op x x)
       grind)
    | exact superpose eq32961 eq688
    | (have j1 := eq32961 X2
       grind)
    | exact resolve eq688 eq32961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688 eq32961
  have eq38204 : ∀ X2 : G, (M.op x y) = (M.op (M.op x y) y) ∨ (k X2 (M.op x y)) = X2 ∨ (σ (M.op x y)) = (σ y) := by
    intro X2
    first
    | (have i₁ := eq38187 x x X2
       have i₂ := eq698 x x
       grind)
    | (have i₁ := eq38187 x y X2
       have i₂ := eq698 x X2
       grind)
    | exact superpose eq698 eq38187
    | (have j0 := eq38187 x y X2
       grind)
    | exact resolve eq38187 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38187
  have eq38263 : ∀ X2 : G, (M.op x y) = (M.op (M.op x y) y) ∨ (k X2 (M.op x y)) = X2 ∨ (σ (M.op x y)) = (σ y) := by
    intro X2
    first
    | (have i₁ := eq38204 X2
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq38204
    | (have j0 := eq38204 X2
       grind)
    | exact resolve eq38204 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38204
  have eq38292 : ∀ X2 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (k X2 (M.op x y)) = X2 ∨ (σ (M.op x y)) = (σ y) := by
    intro X2
    first
    | exact superpose eq36210 eq38263
    | (have j0 := eq38263 X2
       have j1 := eq36210 X2
       grind)
    | exact resolve eq38263 eq36210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36210 eq38263
  have eq38314 : ∀ X2 : G, (k X2 (M.op x y)) = X2 ∨ (σ (M.op x y)) = (σ y) := by
    intro X2
    first
    | (have j0 := eq38292 X2
       have j1 := eq28 X2 (M.op x y)
       grind)
    | (have r₁ := eq38292 X2
       have r₂ := eq28 x (M.op x y)
       grind)
    | exact resolve eq38292 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38292
  have eq38333 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq38314 eq802
    | (have j0 := eq802 (M.op x y)
       grind)
    | (have r₁ := eq802 (M.op x y)
       have r₂ := eq38314 (M.op x y)
       grind)
    | exact resolve eq802 eq38314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38338 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq38314 eq849
    | (have j0 := eq849 (M.op x y)
       grind)
    | exact resolve eq849 eq38314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38314
  have eq38399 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq38338
  have eq38401 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq38333
  have eq38454 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq38399
    | exact resolve eq38399 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38399
  have eq38524 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq38401 eq698
    | exact resolve eq698 eq38401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38532 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq38401 eq38524
    | exact resolve eq38524 eq38401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38401 eq38524
  have eq38812 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq38454 eq698
    | exact resolve eq698 eq38454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38816 : (σ (M.op x y)) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq38454 eq38812
    | exact resolve eq38812 eq38454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38454 eq38812
  have eq38831 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq38532 eq38816
    | exact resolve eq38816 eq38532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38532 eq38816
  have eq38913 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  have eq42705 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) X0) ∨ (k X1 (M.op (σ x) (σ y))) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq712 X0
       have i₂ := eq33071 (M.op sF0 y)
       grind)
    | exact superpose eq33071 eq712
    | (have j1 := eq33071 X1
       grind)
    | exact resolve eq712 eq33071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42764 : ∀ X0 : G, (σ x) = (τ (σ x)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq18973
       have i₂ := eq33071 (M.op sF0 y)
       grind)
    | exact superpose eq33071 eq18973
    | (have j1 := eq33071 X0
       grind)
    | exact resolve eq18973 eq33071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33071
  have eq42806 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq30 eq42764
    | (have j0 := eq42764 X0
       grind)
    | exact resolve eq42764 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42764
  have eq43048 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq42806 eq802
    | (have j0 := eq802 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq802 (M.op (σ x) (σ y))
       have r₂ := eq42806 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq802 eq42806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42806
  have eq43108 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq43048
  have eq43235 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43108 eq698
    | exact resolve eq698 eq43108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43238 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43108 eq43235
    | exact resolve eq43235 eq43108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43108 eq43235
  have eq45358 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq846 y y
       have i₂ := eq33137 X0
       grind)
    | exact superpose eq33137 eq846
    | (have j0 := eq846 y y
       have j1 := eq33137 X0
       grind)
    | exact resolve eq846 eq33137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33137
  have eq45359 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq45358 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45358
  have eq45362 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq45359 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq45359
    | (have j0 := eq45359 X0
       grind)
    | exact resolve eq45359 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45359
  have eq45372 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq36542 eq45362
    | (have j0 := eq45362 X0
       grind)
    | exact resolve eq45362 eq36542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45362
  have eq45380 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq36587 eq45372
    | (have j0 := eq45372 X0
       have j1 := eq36587 (M.op x y)
       grind)
    | exact resolve eq45372 eq36587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45372
  have eq45381 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq45380 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45380
  have eq45469 : (σ x) = (τ (σ x)) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33139 eq18973
    | exact resolve eq18973 eq33139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18973
  have eq45517 : x = (k y y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq45469
    | exact resolve eq45469 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45469
  have eq45776 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq846 y y
       have i₂ := eq45517
       grind)
    | exact superpose eq45517 eq846
    | (have j0 := eq846 y y
       grind)
    | exact resolve eq846 eq45517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45517
  have eq45777 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq45776
  have eq45780 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45777
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq45777
    | exact resolve eq45777 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45777
  have eq45791 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36542 eq45780
    | exact resolve eq45780 eq36542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45780
  have eq45799 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36587 eq45791
    | (have j1 := eq36587 (M.op x y)
       grind)
    | exact resolve eq45791 eq36587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45791
  have eq45800 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq45799
  have eq45870 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45800 eq698
    | exact resolve eq698 eq45800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45873 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43238 eq45870
    | exact resolve eq45870 eq43238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43238 eq45870
  have eq45892 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45800 eq45873
    | exact resolve eq45873 eq45800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45800 eq45873
  have eq45919 : (σ (M.op x y)) ≠ (σ y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45892 eq27
    | exact resolve eq27 eq45892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45928 : (σ y) ≠ (σ y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq26531 eq45919
    | (have r₁ := eq45919
       have r₂ := eq26531
       grind)
    | exact resolve eq45919 eq26531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26531 eq45919
  have eq45931 : (σ y) ≠ (σ y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq45928
  have eq45932 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq45931
  have eq45945 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (σ y) ∨ x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq45932 eq29420
    | exact resolve eq29420 eq45932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29420 eq45932
  have eq45964 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq45945
  have eq45981 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have r₁ := eq45964
       have r₂ := eq26612
       grind)
    | exact resolve eq45964 eq26612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26612 eq45964
  have eq45997 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq45981
    | exact resolve eq45981 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45981
  have eq45998 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by grind
  clear eq45997
  have eq53478 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq42705 X0 (M.op sF2 sF3)
       grind)
    | exact superpose eq42705 eq26
    | (have j1 := eq42705 (σ y) X0
       grind)
    | exact resolve eq26 eq42705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42705
  have eq53547 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53478 eq802
    | (have j0 := eq802 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq802 (M.op (σ x) (σ y))
       have r₂ := eq53478 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq802 eq53478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53478
  have eq53613 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq53547
  have eq53751 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53613 eq698
    | exact resolve eq698 eq53613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53754 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53613 eq53751
    | exact resolve eq53751 eq53613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53613 eq53751
  have eq53881 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53754 eq33139
    | exact resolve eq33139 eq53754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33139
  have eq53906 : x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq53881
  have eq54218 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq53906
       grind)
    | exact superpose eq53906 eq41
    | exact resolve eq41 eq53906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq54231 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq846 y y
       have i₂ := eq53906
       grind)
    | exact superpose eq53906 eq846
    | (have j0 := eq846 y y
       grind)
    | exact resolve eq846 eq53906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq54232 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq54231
  have eq54235 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54232
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq54232
    | exact resolve eq54232 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54232
  have eq54243 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54218
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq54218
    | exact resolve eq54218 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54218
  have eq54247 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36542 eq54235
    | exact resolve eq54235 eq36542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54235
  have eq54254 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54243
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq54243
    | exact resolve eq54243 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54243
  have eq54256 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36587 eq54247
    | (have j1 := eq36587 (M.op x y)
       grind)
    | exact resolve eq54247 eq36587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54247
  have eq54257 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq54256
  have eq54302 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54257 eq179
    | exact resolve eq179 eq54257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq54316 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54257 eq175
    | exact resolve eq175 eq54257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq54333 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54257 eq698
    | exact resolve eq698 eq54257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54336 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53754 eq54333
    | exact resolve eq54333 eq53754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54333
  have eq54357 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq54302
    | exact resolve eq54302 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54302
  have eq54359 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54257 eq54336
    | exact resolve eq54336 eq54257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54257 eq54336
  have eq54395 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54359 eq27
    | exact resolve eq27 eq54359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54407 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq38831 eq54395
    | (have r₁ := eq54395
       have r₂ := eq38831
       grind)
    | exact resolve eq54395 eq38831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54395
  have eq54412 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq54407
  have eq54492 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54316 eq849
    | (have j0 := eq849 (M.op x y)
       grind)
    | exact resolve eq849 eq54316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq54506 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq54492
  have eq54513 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq54506
    | exact resolve eq54506 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54506
  have eq54709 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq38831 eq54357
    | exact resolve eq54357 eq38831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54357
  have eq54749 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq54254 eq54709
    | exact resolve eq54709 eq54254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54254 eq54709
  have eq54751 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq54412 eq54749
    | exact resolve eq54749 eq54412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54412 eq54749
  have eq54753 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have r₁ := eq54751
       have r₂ := eq38913
       grind)
    | exact resolve eq54751 eq38913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54751
  have eq55398 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54513 eq698
    | exact resolve eq698 eq54513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55403 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53754 eq55398
    | exact resolve eq55398 eq53754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53754 eq55398
  have eq55419 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54359 eq55403
    | exact resolve eq55403 eq54359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54359 eq55403
  have eq57062 : (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq55419 eq54513
    | exact resolve eq54513 eq55419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54513 eq55419
  have eq57090 : (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq57062
  have eq57108 : (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54753 eq57090
    | exact resolve eq57090 eq54753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54753 eq57090
  have eq57109 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq57108
  have eq57151 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq57109 eq27
    | exact resolve eq27 eq57109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57109
  have eq57190 : (σ x) ≠ (σ y) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq38831 eq57151
    | exact resolve eq57151 eq38831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57192 : (σ x) ≠ (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have r₁ := eq57190
       have r₂ := eq38913
       grind)
    | exact resolve eq57190 eq38913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38913 eq57190
  have eq67615 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq698 x x
       have i₂ := eq45381 (M.op x x)
       grind)
    | exact superpose eq45381 eq698
    | (have j1 := eq45381 X0
       grind)
    | exact resolve eq698 eq45381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67618 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq45381 eq67615
    | (have j0 := eq67615 X0
       have j1 := eq45381 X0
       grind)
    | exact resolve eq67615 eq45381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45381 eq67615
  have eq68926 : ∀ X0 : G, (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq22539
       have i₂ := eq67618 (M.op sF0 y)
       grind)
    | exact superpose eq67618 eq22539
    | (have j1 := eq67618 X0
       grind)
    | exact resolve eq22539 eq67618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22539 eq67618
  have eq68959 : ∀ X0 : G, (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq68926 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68926
  have eq68969 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq68959 X0
       have j1 := eq28 X0 (σ x)
       grind)
    | (have r₁ := eq68959 X0
       have r₂ := eq28 X0 (σ x)
       grind)
    | exact resolve eq68959 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq68959
  have eq69236 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq68969 eq802
    | (have j0 := eq802 (σ x)
       grind)
    | (have r₁ := eq802 (σ x)
       have r₂ := eq68969 (σ x)
       grind)
    | exact resolve eq802 eq68969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802 eq68969
  have eq69332 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq69236
  have eq69550 : (M.op (σ x) (σ x)) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq69332 eq698
    | exact resolve eq698 eq69332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69553 : (σ x) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq69332 eq69550
    | exact resolve eq69550 eq69332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69332 eq69550
  have eq69703 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq69553 eq36587
    | exact resolve eq36587 eq69553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36587 eq69553
  have eq71328 : (M.op (σ y) (σ y)) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq69703 eq703
    | exact resolve eq703 eq69703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq71335 : (M.op x y) ≠ (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq69703
  have eq71346 : (M.op x y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36542 eq71328
    | exact resolve eq71328 eq36542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36542 eq71328
  have eq120556 : (M.op x y) = (k (σ y) (σ y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq71346 eq11
    | exact resolve eq11 eq71346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71346
  have eq120562 : (M.op x y) = (k (σ y) (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq120556
  have eq120584 : (M.op x y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq120562
       have r₂ := eq71335
       grind)
    | exact resolve eq120562 eq71335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71335 eq120562
  have eq123758 : (M.op x y) = (σ x) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq120584 eq25597
    | exact resolve eq25597 eq120584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25597 eq120584
  have eq123804 : x = (M.op x x) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq123758
  have eq125655 : (M.op x x) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq698 x x
       have i₂ := eq123804
       grind)
    | exact superpose eq123804 eq698
    | exact resolve eq698 eq123804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125665 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34193 eq125655
    | exact resolve eq125655 eq34193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34193 eq125655
  have eq127888 : x = (M.op x y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq123804
       have i₂ := eq125665
       grind)
    | exact superpose eq125665 eq123804
    | exact resolve eq123804 eq125665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123804 eq125665
  have eq127945 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq127888
  have eq128005 : (M.op x y) ≠ (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127945 eq27
    | exact resolve eq27 eq127945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127945
  have eq128090 : (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq128005
       have r₂ := eq23289
       grind)
    | exact resolve eq128005 eq23289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23289 eq128005
  have eq128104 : x = (τ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq128090 eq30
    | exact resolve eq30 eq128090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq128090
  have eq128497 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23895 eq128104
    | exact resolve eq128104 eq23895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23895 eq128104
  have eq128498 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq128497
  have eq128564 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq128498
       grind)
    | exact superpose eq128498 eq18
    | exact resolve eq18 eq128498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128565 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq128498
       grind)
    | exact superpose eq128498 eq24
    | exact resolve eq24 eq128498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq128695 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq53906
       have i₂ := eq128498
       grind)
    | exact superpose eq128498 eq53906
    | exact resolve eq53906 eq128498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53906 eq128498
  have eq128725 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq54316 eq128695
    | exact resolve eq128695 eq54316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54316 eq128695
  have eq128726 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq128725
  have eq128824 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq128565
    | exact resolve eq128565 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128565
  have eq129051 : (M.op x y) = (σ y) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq128824 eq45998
    | exact resolve eq45998 eq128824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129251 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq128726 eq27
    | exact resolve eq27 eq128726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128726
  have eq129268 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq129251
       have r₂ := eq128824
       grind)
    | exact resolve eq129251 eq128824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128824 eq129251
  have eq129280 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129268 eq27
    | exact resolve eq27 eq129268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129281 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq129268 eq696
    | exact resolve eq696 eq129268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq129315 : (σ x) = (σ y) ∨ x = (σ x) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129268 eq45892
    | exact resolve eq45892 eq129268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45892
  have eq129331 : (M.op x y) = (σ x) ∨ x = (σ x) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129051 eq129315
    | exact resolve eq129315 eq129051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129051 eq129315
  have eq129332 : (M.op x y) = (σ x) ∨ x = (σ x) ∨ x = (M.op x y) := by grind
  clear eq129331
  have eq129351 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq129281
    | (have j0 := eq129281 X0
       grind)
    | exact resolve eq129281 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129281
  have eq129354 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq129268 eq129351
    | exact resolve eq129351 eq129268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129268 eq129351
  have eq129361 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq45998 eq129280
    | exact resolve eq129280 eq45998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45998 eq129280
  have eq129366 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq129361
       have r₂ := eq129332
       grind)
    | exact resolve eq129361 eq129332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129332 eq129361
  have eq129456 : (M.op x y) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq128564
       have i₂ := eq129366
       grind)
    | exact superpose eq129366 eq128564
    | exact resolve eq128564 eq129366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128564
  have eq129458 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) := by grind
  clear eq129366
  have eq129460 : (M.op x y) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq129456
       have r₂ := eq129458
       grind)
    | exact resolve eq129456 eq129458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129456
  have eq131201 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129460 eq129354
    | exact resolve eq129354 eq129460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129354 eq129460
  have eq131231 : (M.op x y) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq131201
  have eq131242 : x = (M.op x y) := by
    first
    | (have r₁ := eq131231
       have r₂ := eq129458
       grind)
    | exact resolve eq131231 eq129458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129458 eq131231
  have eq131281 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq131242
       grind)
    | exact superpose eq131242 eq18
    | exact resolve eq18 eq131242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq131282 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq131242
       grind)
    | exact superpose eq131242 eq22
    | exact resolve eq22 eq131242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq131242
  have eq131394 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq131282 eq20
    | exact resolve eq20 eq131282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq131282
  have eq131947 : (σ x) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq38831 eq131394
    | exact resolve eq131394 eq38831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38831
  have eq132068 : (σ x) ≠ (σ x) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq131394 eq57151
    | (have r₁ := eq57151
       have r₂ := eq131394
       grind)
    | exact resolve eq57151 eq131394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57151 eq131394
  have eq132081 : (M.op x y) = (σ x) := by grind
  clear eq132068
  have eq132170 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have r₁ := eq131947
       have r₂ := eq57192
       grind)
    | exact resolve eq131947 eq57192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57192 eq131947
  have eq132294 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq132081 eq26
    | exact resolve eq26 eq132081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq132081
  have eq135971 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op x y) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq131281 eq700
    | exact resolve eq700 eq131281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq135973 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq131281 eq712
    | exact resolve eq712 eq131281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq136119 : (M.op x y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq135973 eq135971
    | exact resolve eq135971 eq135973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135971 eq135973
  have eq137589 : (M.op (M.op x y) y) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq136119 eq698
    | exact resolve eq698 eq136119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698 eq136119
  have eq137594 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq132294 eq137589
    | exact resolve eq137589 eq132294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132294 eq137589
  have eq137605 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq131281 eq137594
    | exact resolve eq137594 eq131281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131281 eq137594
  have eq137622 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq137605 eq27
    | exact resolve eq27 eq137605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq137605
  have eq137676 : False := by grind
  exact eq137676

/-- `Equation4401`: `x ◇ (x ◇ y) = (x ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_y_pyx_pxx_pyx_Equation4401 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4401 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4401.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X0) := by
    intro X0 X1 X2
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y
       grind)
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | (have i₁ := eq51 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq51
    | (have j0 := eq51 y
       grind)
    | exact resolve eq51 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq142 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq153 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq73 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq73
    | exact resolve eq73 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq175 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) X0) = (M.op X0 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X0 (M.op X0 x) X3
       have i₂ := eq16 X0 x X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X0 x X3
       have i₂ := eq16 X0 x X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq16 X0 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : (M.op (M.op x y) x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq180 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq180
    | (have j0 := eq180 y
       grind)
    | exact resolve eq180 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq692 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq182
    | (have j0 := eq182 (σ x) X0 (σ y)
       grind)
    | exact resolve eq182 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq754 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) X1) (σ x)) := by
    intro X1
    first
    | exact superpose eq692 eq16
    | (have j0 := eq16 (σ x) (σ y) X1
       grind)
    | exact resolve eq16 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq946 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = (M.op X1 (k X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq947 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (k X0 X1) X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq955 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq28 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq28 X1 X1
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq972 : (M.op x y) = (k y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq984 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq991 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1014 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq955 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq955 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq955 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq1093 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1105 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq1093
    | (have j1 := eq28 (σ x) (σ x)
       grind)
    | (have r₁ := eq1093
       have r₂ := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq1093 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq1122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq972
       grind)
    | exact superpose eq972 eq40
    | exact resolve eq40 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq972
  have eq1123 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1122
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1122
    | exact resolve eq1122 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122
  have eq1125 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq1123
    | exact resolve eq1123 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123
  have eq1132 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq991 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq991
    | (have j0 := eq991 (σ X0)
       grind)
    | exact resolve eq991 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1135 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1125 eq984
    | exact resolve eq984 eq1125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984
  have eq1142 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq1135
       have r₂ := eq27
       grind)
    | exact resolve eq1135 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq1147 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1142 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1142
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1142
       grind)
    | exact resolve eq12 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1148 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1142 eq16
    | exact resolve eq16 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1149 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1142 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1151 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1142 eq177
    | exact resolve eq177 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1153 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1142 eq182
    | exact resolve eq182 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1154 : (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq1147
  have eq1155 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ y) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1142 eq1153
    | exact resolve eq1153 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153
  have eq1157 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq1151
    | (have j0 := eq1151 X0
       grind)
    | exact resolve eq1151 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151
  have eq1159 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq1149
    | exact resolve eq1149 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149
  have eq1160 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq1148
    | (have j0 := eq1148 X0
       grind)
    | exact resolve eq1148 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148
  have eq1161 : (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28 eq1154
    | (have j1 := eq28 (σ y) (σ y)
       grind)
    | exact resolve eq1154 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154
  have eq1163 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1155 eq1160
    | exact resolve eq1160 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160
  have eq1164 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1125 eq1161
    | exact resolve eq1161 eq1125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125 eq1161
  have eq1167 : ∀ X0 : G, (M.op x y) = (M.op y (M.op y X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 x
       have i₂ := eq1163
       grind)
    | exact superpose eq1163 eq16
    | exact resolve eq16 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1168 : x = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq1163
       grind)
    | exact superpose eq1163 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1170 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq177 y X0 x
       have i₂ := eq1163
       grind)
    | exact superpose eq1163 eq177
    | exact resolve eq177 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1172 : ∀ X0 : G, (M.op y x) = (M.op y (M.op y X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq182 y X0 x
       have i₂ := eq1163
       grind)
    | exact superpose eq1163 eq182
    | exact resolve eq182 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1174 : ∀ X0 : G, x = (M.op y (M.op y X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1163 eq1172
    | exact resolve eq1172 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq1176 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1170 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1170
    | (have j0 := eq1170 X0
       grind)
    | exact resolve eq1170 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170
  have eq1178 : x = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1168
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1168
    | exact resolve eq1168 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168
  have eq1179 : ∀ X0 : G, (M.op x y) = (M.op y (M.op y X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1167 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1167
    | (have j0 := eq1167 X0
       grind)
    | exact resolve eq1167 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167
  have eq1193 : ∀ X1 : G, x = (M.op (M.op y X1) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq16 y x X1
       have i₂ := eq1174 x
       grind)
    | exact superpose eq1174 eq16
    | exact resolve eq16 eq1174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1197 : ∀ X0 : G, x = (k (M.op y X0) y) ∨ y = (M.op (M.op y X0) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op y X0) y
       have i₂ := eq1174 X0
       grind)
    | exact superpose eq1174 eq28
    | (have j0 := eq28 (M.op y X0) y
       grind)
    | exact resolve eq28 eq1174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1201 : ∀ X0 : G, (M.op y x) = (M.op y (M.op y X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq182 y X0 (M.op y x)
       have i₂ := eq1174 x
       grind)
    | exact superpose eq1174 eq182
    | exact resolve eq182 eq1174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174
  have eq1204 : (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1179 eq1201
    | exact resolve eq1201 eq1179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201
  have eq1208 : ∀ X0 : G, x = (k (M.op y X0) y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1176 eq1197
    | (have j0 := eq1197 X0
       grind)
    | exact resolve eq1197 eq1176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197
  have eq1212 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1176 eq1193
    | exact resolve eq1193 eq1176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193
  have eq1220 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1212 eq27
    | exact resolve eq27 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1229 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq1204
       grind)
    | exact superpose eq1204 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq1204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204
  have eq1241 : y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1229
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1229
    | exact resolve eq1229 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229
  have eq1247 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1212 eq1241
    | exact resolve eq1241 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241
  have eq1336 : ∀ X0 : G, (M.op x y) = (k (M.op y X0) y) ∨ y = (M.op (M.op y X0) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op y X0) y
       have i₂ := eq1179 X0
       grind)
    | exact superpose eq1179 eq28
    | (have j0 := eq28 (M.op y X0) y
       grind)
    | exact resolve eq28 eq1179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179
  have eq1354 : ∀ X0 : G, (M.op x y) = (k (M.op y X0) y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1176 eq1336
    | (have j0 := eq1336 X0
       grind)
    | exact resolve eq1336 eq1176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176 eq1336
  have eq1365 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1178
       grind)
    | exact superpose eq1178 eq41
    | exact resolve eq41 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq1366 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1365
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1365
    | exact resolve eq1365 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1365
  have eq1377 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1247 eq41
    | exact resolve eq41 eq1247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1247
  have eq1378 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1377
    | exact resolve eq1377 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377
  have eq1393 : ∀ X0 : G, (σ x) = (M.op (σ y) (k X0 (σ y))) ∨ x = (M.op y x) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1155 X0
       have i₂ := eq28 X0 sF3
       grind)
    | exact superpose eq28 eq1155
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq1155 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1400 : ∀ X1 : G, (σ x) = (M.op (M.op (σ y) X1) (σ y)) ∨ x = (M.op y x) := by
    intro X1
    first
    | exact superpose eq1155 eq16
    | exact resolve eq16 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1427 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (k X0 (σ y)) (σ y)) ∨ x = (M.op y x) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1157 X0
       have i₂ := eq28 X0 sF3
       grind)
    | exact superpose eq28 eq1157
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq1157 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157
  have eq1454 : ∀ X0 : G, (σ x) = (M.op (k X0 (σ y)) (σ y)) ∨ x = (M.op y x) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq1163 eq1427
    | (have j0 := eq1427 X0
       grind)
    | exact resolve eq1427 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1427
  have eq1540 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1159 eq153
    | exact resolve eq153 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159
  have eq1541 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30 eq1540
    | exact resolve eq1540 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1540
  have eq1544 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1163 eq1541
    | exact resolve eq1541 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1541
  have eq1549 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1544
       grind)
    | exact superpose eq1544 eq41
    | exact resolve eq41 eq1544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1550 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1549
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1549
    | exact resolve eq1549 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1549
  have eq1562 : ∀ X0 : G, (σ x) = (k (σ (M.op y X0)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41 (M.op y X0)
       have i₂ := eq1208 X0
       grind)
    | exact superpose eq1208 eq41
    | exact resolve eq41 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq1568 : ∀ X0 : G, (σ x) = (k (σ (M.op y X0)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1562 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1562
    | (have j0 := eq1562 X0
       grind)
    | exact resolve eq1562 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1562
  have eq1586 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op y X0)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41 (M.op y X0)
       have i₂ := eq1354 X0
       grind)
    | exact superpose eq1354 eq41
    | exact resolve eq41 eq1354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1354
  have eq1594 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op y X0)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq1586
    | (have j0 := eq1586 X0
       grind)
    | exact resolve eq1586 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1586
  have eq1598 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1568 eq1594
    | exact resolve eq1594 eq1568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1568 eq1594
  have eq1641 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = (M.op X1 (M.op (k X0 X1) X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq175 X1 X0 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq175
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq175 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq1924 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1164 eq1155
    | exact resolve eq1155 eq1164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155
  have eq1931 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1164 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) x
       have r₂ := eq1164
       grind)
    | exact resolve eq13 eq1164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1932 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq1931 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1931
  have eq1933 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq1924
  have eq2006 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq1933 eq1164
    | exact resolve eq1164 eq1933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1164 eq1933
  have eq2022 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq2006
  have eq2038 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2022 eq991
    | (have j0 := eq991 (σ y)
       grind)
    | exact resolve eq991 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2758 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2022 eq1393
    | (have j0 := eq1393 (σ y)
       grind)
    | exact resolve eq1393 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393
  have eq2778 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) := by grind
  clear eq2758
  have eq2817 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2022 eq1454
    | (have j0 := eq1454 (σ y)
       grind)
    | exact resolve eq1454 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1454
  have eq2828 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq2817
  have eq2900 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1932 eq26
    | (have j1 := eq1932 (σ x)
       grind)
    | exact resolve eq26 eq1932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1932
  have eq2937 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2022 eq2900
    | exact resolve eq2900 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2022 eq2900
  have eq2976 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1163 eq2937
    | exact resolve eq2937 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163 eq2937
  have eq3062 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2976 eq1014
    | (have j0 := eq1014 (σ x) X0
       grind)
    | (have r₁ := eq1014 (σ x) x
       have r₂ := eq2976
       grind)
    | exact resolve eq1014 eq2976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2976
  have eq3065 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq3062 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3062
  have eq3360 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq3065 eq1142
    | exact resolve eq1142 eq3065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142 eq3065
  have eq3372 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq3360
  have eq3386 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1550 eq3372
    | exact resolve eq3372 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1550 eq3372
  have eq3500 : (τ (σ x)) = (k (τ (σ x)) y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq3386 eq153
    | exact resolve eq153 eq3386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq3386
  have eq3503 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (k x y) := by
    first
    | exact superpose eq30 eq3500
    | exact resolve eq3500 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3500
  have eq4475 : ∀ X0 : G, (M.op x y) = (M.op y (M.op y X0)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq947 x y X0
       have i₂ := eq1544
       grind)
    | exact superpose eq1544 eq947
    | (have j0 := eq947 x y x
       grind)
    | exact resolve eq947 eq1544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544
  have eq4497 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1366 eq947
    | (have j0 := eq947 (σ x) (σ y) x
       grind)
    | exact resolve eq947 eq1366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq4649 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq4497
    | (have j0 := eq4497 X0
       grind)
    | exact resolve eq4497 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4497
  have eq4660 : ∀ X0 : G, (M.op x y) = (M.op y (M.op y X0)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq4475 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4475
    | (have j0 := eq4475 X0
       grind)
    | exact resolve eq4475 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4475
  have eq4705 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq4649
    | (have j0 := eq4649 X0
       grind)
    | exact resolve eq4649 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4649
  have eq4715 : ∀ X0 : G, (M.op x y) = (M.op y (M.op y X0)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq4660 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4660
    | (have j0 := eq4660 X0
       grind)
    | exact resolve eq4660 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4660
  have eq4761 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4705 eq4705
    | exact resolve eq4705 eq4705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4705
  have eq4813 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4761
  have eq4978 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq4715 (M.op y x)
       have i₂ := eq4715 x
       grind)
    | exact superpose eq4715 eq4715
    | exact resolve eq4715 eq4715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5024 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 (M.op y x)
       have i₂ := eq4715 x
       grind)
    | exact superpose eq4715 eq16
    | exact resolve eq16 eq4715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5041 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq4978
  have eq5047 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq4715 eq5024
    | exact resolve eq5024 eq4715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4715 eq5024
  have eq5078 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq5041 eq28
    | (have j0 := eq28 (M.op x y) y
       grind)
    | exact resolve eq28 eq5041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5041
  have eq5095 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq5047 eq5078
    | exact resolve eq5078 eq5047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5047 eq5078
  have eq5096 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq5095
  have eq5118 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq5096 eq41
    | exact resolve eq41 eq5096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq5122 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq5118
    | exact resolve eq5118 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5118
  have eq5165 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2778 eq1400
    | exact resolve eq1400 eq2778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5184 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) := by grind
  clear eq5165
  have eq5278 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2828 eq1400
    | exact resolve eq1400 eq2828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400
  have eq5297 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5278
  have eq17683 : (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5184 eq2778
    | exact resolve eq2778 eq5184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2778 eq5184
  have eq17722 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq17683
  have eq17758 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17722 eq28
    | (have j0 := eq28 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq28 eq17722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17722
  have eq17820 : (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5297 eq2828
    | exact resolve eq2828 eq5297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2828 eq5297
  have eq17861 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq17820
  have eq21212 : (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17758 eq17861
    | exact resolve eq17861 eq17758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17758
  have eq21257 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq21212
  have eq21286 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21257 eq5122
    | exact resolve eq5122 eq21257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5122
  have eq21289 : (τ (σ x)) = (k (M.op x y) y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21257 eq133
    | exact resolve eq133 eq21257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq21257
  have eq21300 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq21286
  have eq21307 : x = (k (M.op x y) y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq30 eq21289
    | exact resolve eq21289 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21289
  have eq21316 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21307 eq5096
    | exact resolve eq5096 eq21307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5096 eq21307
  have eq21329 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq21316
  have eq21363 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq177 y X0 x
       have i₂ := eq21300
       grind)
    | exact superpose eq21300 eq177
    | exact resolve eq177 eq21300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq21368 : ∀ X0 : G, (M.op y x) = (M.op y (M.op y X0)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq182 y X0 x
       have i₂ := eq21300
       grind)
    | exact superpose eq21300 eq182
    | exact resolve eq182 eq21300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq21393 : ∀ X0 : G, x = (M.op y (M.op y X0)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq21300 eq21368
    | exact resolve eq21368 eq21300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21300 eq21368
  have eq21398 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq21363 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21363
    | (have j0 := eq21363 X0
       grind)
    | exact resolve eq21363 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21363
  have eq22090 : ∀ X1 : G, x = (M.op (M.op y X1) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X1
    first
    | (have i₁ := eq16 y x X1
       have i₂ := eq21393 x
       grind)
    | exact superpose eq21393 eq16
    | exact resolve eq16 eq21393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21393
  have eq22187 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21398 eq22090
    | exact resolve eq22090 eq21398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21398 eq22090
  have eq22216 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22187
       have r₂ := eq1220
       grind)
    | exact resolve eq22187 eq1220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22187
  have eq22246 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22216 eq26
    | exact resolve eq26 eq22216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22247 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22216 eq32
    | exact resolve eq32 eq22216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq22332 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq22247
    | exact resolve eq22247 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22247
  have eq22333 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1212 eq22246
    | exact resolve eq22246 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212 eq22246
  have eq22344 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq22332
       grind)
    | exact superpose eq22332 eq18
    | exact resolve eq18 eq22332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22345 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq22332
       grind)
    | exact superpose eq22332 eq24
    | exact resolve eq24 eq22332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22332
  have eq22414 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq22345
    | exact resolve eq22345 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22345
  have eq22415 : (M.op x y) = (M.op (M.op x y) x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq183 eq22344
    | exact resolve eq22344 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq22344
  have eq22426 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq22414 eq1220
    | exact resolve eq1220 eq22414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22430 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq22414 eq2038
    | (have r₁ := eq2038
       have r₂ := eq22414
       grind)
    | exact resolve eq2038 eq22414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2038
  have eq22491 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq22414 eq17861
    | exact resolve eq17861 eq22414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17861 eq22414
  have eq22512 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq22430
  have eq22514 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq22426
  have eq22528 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21329 eq22491
    | exact resolve eq22491 eq21329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22491
  have eq22529 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq22528
  have eq22549 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21329 eq22512
    | exact resolve eq22512 eq21329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21329 eq22512
  have eq22550 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq22549
  have eq22571 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22216 eq22529
    | exact resolve eq22529 eq22216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22529
  have eq22583 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22216 eq22550
    | exact resolve eq22550 eq22216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22216 eq22550
  have eq22595 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22571 eq22583
    | exact resolve eq22583 eq22571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22571 eq22583
  have eq22596 : x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq22595
  have eq22617 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22333 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq22333
       grind)
    | exact resolve eq13 eq22333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22637 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq22617 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22617
  have eq22715 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22596 eq22415
    | exact resolve eq22415 eq22596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22415 eq22596
  have eq22759 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq22715
  have eq22780 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq22759
       have r₂ := eq22514
       grind)
    | exact resolve eq22759 eq22514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22514 eq22759
  have eq22795 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq22780
       grind)
    | exact superpose eq22780 eq22
    | exact resolve eq22 eq22780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22821 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq22795
    | exact resolve eq22795 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22795
  have eq24172 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22637 eq22333
    | exact resolve eq22333 eq22637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22333 eq22637
  have eq24200 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq24172
  have eq24226 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22780 eq24200
    | exact resolve eq24200 eq22780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24200
  have eq24227 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq24226
  have eq24524 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24227 eq3503
    | exact resolve eq3503 eq24227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3503
  have eq24529 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24227 eq142
    | exact resolve eq142 eq24227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq24227
  have eq24538 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq24529
    | exact resolve eq24529 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq24529
  have eq24541 : x = (M.op y x) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq24524
       have r₂ := eq1220
       grind)
    | exact resolve eq24524 eq1220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220 eq24524
  have eq24543 : x = (M.op x x) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22780 eq24541
    | exact resolve eq24541 eq22780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24541
  have eq24545 : x = (M.op x x) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22780 eq24543
    | exact resolve eq24543 eq22780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24543
  have eq24547 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq991 x
       grind)
    | (have r₁ := eq24545
       have r₂ := eq991 x
       grind)
    | exact resolve eq24545 eq991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24545
  have eq24618 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1014 x X0
       have i₂ := eq24538
       grind)
    | exact superpose eq24538 eq1014
    | (have j0 := eq1014 x X0
       grind)
    | (have r₁ := eq1014 x x
       have r₂ := eq24538
       grind)
    | exact resolve eq1014 eq24538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014 eq24538
  have eq24625 : ∀ X0 : G, (k x X0) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq24618 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24618
  have eq168045 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op (σ y) (M.op (σ (M.op x y)) (σ y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1378 eq1641
    | (have j0 := eq1641 (σ (M.op x y)) (σ y) x
       grind)
    | exact resolve eq1641 eq1378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1641
  have eq169091 : (M.op (σ y) (k (σ (M.op x y)) (σ y))) = (M.op (σ y) (M.op (σ (M.op x y)) (σ y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq946 eq168045
    | (have j1 := eq946 (σ (M.op x y)) (σ y) x
       grind)
    | exact resolve eq168045 eq946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946 eq168045
  have eq169640 : (M.op (σ y) (σ (M.op x y))) = (M.op (σ y) (M.op (σ (M.op x y)) (σ y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1378 eq169091
    | exact resolve eq169091 eq1378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169091
  have eq169994 : (k (σ (M.op x y)) (σ y)) = (M.op (σ y) (M.op (σ (M.op x y)) (σ y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq169640
    | (have j1 := eq28 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq169640 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq169640
  have eq170228 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) (σ y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1378 eq169994
    | exact resolve eq169994 eq1378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378 eq169994
  have eq170331 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1598 eq170228
    | exact resolve eq170228 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170228
  have eq170384 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq170331
    | exact resolve eq170331 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170331
  have eq170400 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1598 eq170384
    | exact resolve eq170384 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1598 eq170384
  have eq170410 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq170400
    | exact resolve eq170400 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170400
  have eq170793 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq170410 eq4813
    | exact resolve eq4813 eq170410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4813 eq170410
  have eq170864 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq170793
  have eq170917 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq170864 eq1105
    | (have r₁ := eq1105
       have r₂ := eq170864
       grind)
    | exact resolve eq1105 eq170864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105
  have eq170931 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq170933 : (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq170917
  have eq170935 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1366 eq170933
    | exact resolve eq170933 eq1366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1366 eq170933
  have eq170941 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq991 (σ x)
       grind)
    | (have r₁ := eq170935
       have r₂ := eq991 (σ x)
       grind)
    | exact resolve eq170935 eq991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991 eq170935
  have eq171100 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq170941 eq754
    | exact resolve eq754 eq170941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq171188 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq170864 eq171100
    | exact resolve eq171100 eq170864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171100
  have eq171205 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq171188
    | exact resolve eq171188 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171188
  have eq171219 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq170864 eq171205
    | exact resolve eq171205 eq170864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170864 eq171205
  have eq171233 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq170941 eq171219
    | exact resolve eq171219 eq170941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170941 eq171219
  have eq171249 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq171233
       have r₂ := eq170931
       grind)
    | exact resolve eq171233 eq170931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170931 eq171233
  have eq171264 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq171249 eq27
    | exact resolve eq27 eq171249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171249
  have eq171288 : (σ x) ≠ (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq22821 eq171264
    | (have r₁ := eq171264
       have r₂ := eq22821
       grind)
    | exact resolve eq171264 eq22821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22821 eq171264
  have eq171290 : y = (M.op x y) ∨ x = y := by grind
  clear eq171288
  have eq171348 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq171290
  have eq171358 : x = y := by
    first
    | (have r₁ := eq171348
       have r₂ := eq22780
       grind)
    | exact resolve eq171348 eq22780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22780 eq171348
  have eq171427 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq171358
       grind)
    | exact superpose eq171358 eq18
    | exact resolve eq18 eq171358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq171428 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq171358
       grind)
    | exact superpose eq171358 eq24
    | exact resolve eq24 eq171358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq171358
  have eq171562 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq171428
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq171428
    | exact resolve eq171428 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171428
  have eq171591 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq171562 eq26
    | exact resolve eq26 eq171562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq171562
  have eq171732 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24547
       have i₂ := eq171427
       grind)
    | exact superpose eq171427 eq24547
    | exact resolve eq24547 eq171427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24547
  have eq171758 : ∀ X0 : G, x ≠ (M.op x y) ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq171427
       grind)
    | exact superpose eq171427 eq13
    | (have j0 := eq13 x X0
       grind)
    | exact resolve eq13 eq171427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171810 : x = (M.op x y) := by grind
  clear eq171732
  have eq171850 : ∀ X0 : G, (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq171758 X0
       have j1 := eq24625 X0
       grind)
    | (have r₁ := eq171758 X0
       have r₂ := eq24625 X0
       grind)
    | exact resolve eq171758 eq24625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24625 eq171758
  have eq171879 : ∀ X0 : G, (k (M.op x y) X0) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq171850 X0
       have i₂ := eq171810
       grind)
    | exact superpose eq171810 eq171850
    | exact resolve eq171850 eq171810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171850
  have eq171906 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq171810
       grind)
    | exact superpose eq171810 eq22
    | exact resolve eq22 eq171810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq172023 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq171427
       have i₂ := eq171810
       grind)
    | exact superpose eq171810 eq171427
    | exact resolve eq171427 eq171810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171427 eq171810
  have eq172026 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq171879 eq172023
    | exact resolve eq172023 eq171879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171879 eq172023
  have eq172082 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq171906 eq20
    | exact resolve eq20 eq171906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171906
  have eq172773 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq172026 eq1132
    | (have j0 := eq1132 (M.op x y)
       grind)
    | exact resolve eq1132 eq172026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132 eq172026
  have eq172783 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq172773
  have eq172792 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq172783
    | exact resolve eq172783 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq172783
  have eq172798 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq172082 eq172792
    | exact resolve eq172792 eq172082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172792
  have eq172810 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq172798 eq171591
    | exact resolve eq171591 eq172798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171591 eq172798
  have eq172944 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq172810 eq27
    | exact resolve eq27 eq172810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq172810
  have eq172956 : False := by grind
  exact eq172956

/-- `Equation4412`: `x ◇ (x ◇ y) = (y ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pyx_x_pyx_Equation4412 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4412 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4412.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X1) := by
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
  have eq30 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq25
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq25
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
  clear eq36
  have eq50 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X3) (M.op X2 X0)) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X2 X0) X3
       have i₂ := eq14 X2 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X3) X1) = (M.op (M.op X1 X2) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X2) X1 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 x X0 X3
       have i₂ := eq14 x X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3 (M.op X3 X0)
       have i₂ := eq14 X3 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 (M.op X0 x)) = (M.op (M.op x y) x) := by
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
  have eq58 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq14 X2 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq86 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq74
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq98
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq110
    | exact resolve eq110 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq129 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq189 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq206 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op x X1) (M.op X0 (M.op X0 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op x X1)
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq56 x
       have i₂ := eq14 x x X0
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op x y) x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X1 x)
       have i₂ := eq56 X1
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (M.op x X1) (M.op (M.op x y) x)) := by
    intro X1
    first
    | (have i₁ := eq206 x X1
       have i₂ := eq56 x
       grind)
    | exact superpose eq56 eq206
    | exact resolve eq206 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq231 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 X0
       have i₂ := eq11 (τ X1) X0
       grind)
    | exact superpose eq11 eq35
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq35 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  clear eq39
  have eq348 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 (M.op X0 x) X1
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) x)) = (M.op X1 (M.op X1 (M.op X0 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 (M.op X0 x) X1
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq417 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq58 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq58
    | (have j0 := eq58 x y X0
       grind)
    | exact resolve eq58 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq58
    | (have j0 := eq58 X0 (σ y) (σ x)
       grind)
    | exact resolve eq58 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq444 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X2 X3 (M.op X2 X1)
       have i₂ := eq58 X2 X1 X0
       grind)
    | (have i₁ := eq53 X2 X3 (M.op X2 X1)
       have i₂ := eq58 X0 X1 X2
       grind)
    | exact superpose eq58 eq53
    | exact resolve eq53 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3 (M.op X3 X1)
       have i₂ := eq58 X3 X1 X0
       grind)
    | (have i₁ := eq14 X2 X3 (M.op X3 X1)
       have i₂ := eq58 X0 X1 X3
       grind)
    | exact superpose eq58 eq14
    | exact resolve eq14 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X0 X1))) = (M.op (M.op (M.op X2 X1) X3) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X2 X1) X3
       have i₂ := eq58 X2 X1 X0
       grind)
    | (have i₁ := eq14 X2 (M.op X2 X1) X3
       have i₂ := eq58 X0 X1 X2
       grind)
    | exact superpose eq58 eq14
    | exact resolve eq14 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq471 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X0 X1))) = (M.op (M.op (M.op X3 X4) X3) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq54 X3 X4 (M.op X1 X2) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X1 X2 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op X1 X2) X1) x) := by
    intro X1 X2
    first
    | (have i₁ := eq54 X1 X2 x x
       have i₂ := eq56 x
       grind)
    | exact superpose eq56 eq54
    | exact resolve eq54 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq519 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X4) X3) = (M.op (M.op (M.op (M.op X0 X1) X0) X2) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X3 (M.op X3 X2) X4
       have i₂ := eq54 X0 X1 X3 X2
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq521 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op (M.op X0 X1) X0) X2)) = (M.op X4 (M.op X4 (M.op X3 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq58 X3 (M.op X3 X2) X4
       have i₂ := eq54 X0 X1 X3 X2
       grind)
    | exact superpose eq54 eq58
    | exact resolve eq58 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq527 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X0 (M.op (M.op X1 X2) X1))) (M.op (M.op X1 X2) X1)) = (M.op (M.op (M.op X1 X2) X1) (M.op X0 (M.op X0 (M.op (M.op X1 X2) X1)))) := by
    intro X0 X1 X2
    grind
  have eq557 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X1 y)
       have i₂ := eq417 X1
       grind)
    | (have i₁ := eq14 X0 x (M.op x y)
       have i₂ := eq417 X0
       grind)
    | exact superpose eq417 eq14
    | exact resolve eq14 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq570 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X0 X1)) X2) = (M.op (M.op X2 X3) (M.op X4 (M.op X4 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X4 X2 X3 (M.op X2 X1)
       have i₂ := eq58 X2 X1 X0
       grind)
    | (have i₁ := eq52 X4 X2 X3 (M.op X2 X1)
       have i₂ := eq58 X0 X1 X2
       grind)
    | exact superpose eq58 eq52
    | exact resolve eq52 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) x) X0) = (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X2 X0 X1 (M.op X0 x)
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq52
    | exact resolve eq52 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq623 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X2 X4) (M.op (M.op (M.op X0 X1) X0) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 x X2 X4 X3
       have i₂ := eq54 X0 X1 x X2
       grind)
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    grind
  clear eq52
  have eq693 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq418 X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq418
    | (have j1 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq418 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq730 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) X1)) = (M.op (M.op (M.op x y) x) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X1 X2 X0 (M.op (M.op X0 X1) x)
       have i₂ := eq56 (M.op X0 X1)
       grind)
    | exact superpose eq56 eq51
    | exact resolve eq51 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq782 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 (M.op X0 X1)) X4) (M.op X3 (M.op X0 X1))) = (M.op X3 (M.op X0 (M.op (M.op X1 X2) X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq51 (M.op X0 X1) x X3 X4
       have i₂ := eq51 X1 X2 X0 x
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq786 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X2) X1))) = (M.op (M.op (M.op (M.op (M.op X3 X4) X3) X1) X5) (M.op (M.op (M.op X3 X4) X3) X1)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq51 X1 X2 (M.op (M.op X3 X4) X3) X5
       have i₂ := eq54 X3 X4 X0 (M.op (M.op X1 X2) X1)
       grind)
    | exact superpose eq54 eq51
    | exact resolve eq51 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq54
  have eq1114 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq1131 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq92 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq1132 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1131 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131
  have eq1134 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1114 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114
  have eq1136 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1134 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq1134
    | (have j0 := eq1134 X0
       grind)
    | exact resolve eq1134 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134
  have eq1235 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq693 (M.op sF3 y)
       have i₂ := eq417 sF3
       grind)
    | exact superpose eq417 eq693
    | exact resolve eq693 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1610 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op (M.op x y) x) (M.op X0 (M.op X0 y))) := by
    intro X0
    first
    | exact superpose eq209 eq417
    | exact resolve eq417 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1615 : (M.op x (M.op x y)) = (M.op (M.op (M.op x y) x) (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq1610 x
       have i₂ := eq417 x
       grind)
    | (have i₁ := eq1610 x
       have i₂ := eq417 x
       grind)
    | exact superpose eq417 eq1610
    | (have j0 := eq1610 x
       grind)
    | exact resolve eq1610 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1610
  have eq1688 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op x y) x)) := by
    first
    | exact superpose eq418 eq211
    | exact resolve eq211 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq2065 : ∀ X0 : G, (M.op (M.op (M.op x y) x) X0) = (M.op (M.op x (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq348 X0 (M.op X0 y)
       have i₂ := eq417 X0
       grind)
    | (have i₁ := eq348 x (M.op x y)
       have i₂ := eq417 X0
       grind)
    | exact superpose eq417 eq348
    | exact resolve eq348 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3421 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (M.op X0 (M.op X0 y))) := by
    intro X0
    first
    | exact superpose eq557 eq417
    | exact resolve eq417 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq3426 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq3421 x
       have i₂ := eq417 x
       grind)
    | (have i₁ := eq3421 x
       have i₂ := eq417 x
       grind)
    | exact superpose eq417 eq3421
    | (have j0 := eq3421 x
       grind)
    | exact resolve eq3421 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3421
  have eq5543 : ∀ X1 X2 : G, (M.op x (M.op x y)) = (M.op (M.op X1 (M.op X1 X2)) y) := by
    intro X1 X2
    first
    | (have i₁ := eq446 X1 X2 x y
       have i₂ := eq417 x
       grind)
    | (have i₁ := eq446 x X1 x y
       have i₂ := eq417 x
       grind)
    | exact superpose eq417 eq446
    | (have j0 := eq446 X1 X2 x y
       grind)
    | exact resolve eq446 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq5545 : ∀ X1 X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op X1 (M.op X1 X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq418 eq446
    | (have j0 := eq446 X1 X2 (σ x) (σ y)
       grind)
    | exact resolve eq446 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq23374 : ∀ X0 X1 X2 : G, (M.op (M.op x (M.op x y)) X0) = (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2065 eq573
    | exact resolve eq573 eq2065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq25791 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) X1)) = (M.op (M.op x (M.op x y)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq2065 eq730
    | exact resolve eq730 eq2065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq32143 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1132 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq1132
    | (have j0 := eq1132 (τ X0)
       grind)
    | exact resolve eq1132 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq32153 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq32143 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq32143
    | (have j0 := eq32143 X0
       grind)
    | exact resolve eq32143 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32143
  have eq32159 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq32153 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq32153
    | (have j0 := eq32153 X0
       grind)
    | exact resolve eq32153 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32153
  have eq36413 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X0 X1))) = (M.op (M.op (M.op x y) x) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq447 X0 X1 X2 x
       have i₂ := eq348 (M.op X2 X1) x
       grind)
    | (have i₁ := eq447 X0 y x x
       have i₂ := eq348 (M.op x y) X1
       grind)
    | exact superpose eq348 eq447
    | exact resolve eq447 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq36414 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X0 X1))) = (M.op (M.op x (M.op x y)) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq2065 eq36413
    | exact resolve eq36413 eq2065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36413
  have eq45025 : ∀ X1 X3 X4 : G, (M.op (M.op (M.op X3 X4) X3) X1) = (M.op (M.op x (M.op x y)) X1) := by
    intro X1 X3 X4
    first
    | (have i₁ := eq471 x X1 x X3 X4
       have i₂ := eq23374 X1 x x
       grind)
    | exact superpose eq23374 eq471
    | exact resolve eq471 eq23374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq50764 : ∀ X2 X3 X4 : G, (M.op X4 (M.op X4 (M.op X3 X2))) = (M.op X3 (M.op (M.op x (M.op x y)) X2)) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq521 x x X2 X3 X4
       have i₂ := eq45025 X2 x x
       grind)
    | exact superpose eq45025 eq521
    | exact resolve eq521 eq45025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq51287 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X0 (M.op (M.op x (M.op x y)) X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq444 x (M.op X0 X1) X2 X3
       have i₂ := eq50764 X1 X0 x
       grind)
    | exact superpose eq50764 eq444
    | exact resolve eq444 eq50764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq51345 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) x) X2) = (M.op (M.op X0 (M.op (M.op x (M.op x y)) X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq348 X2 (M.op X2 (M.op X0 X1))
       have i₂ := eq50764 X1 X0 X2
       grind)
    | exact superpose eq50764 eq348
    | exact resolve eq348 eq50764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51378 : ∀ X0 X1 X2 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op X0 (M.op (M.op x (M.op x y)) X1)) X2) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq479 X2 (M.op X2 (M.op X0 X1))
       have i₂ := eq50764 X1 X0 X2
       grind)
    | exact superpose eq50764 eq479
    | exact resolve eq479 eq50764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479 eq50764
  have eq51885 : ∀ X0 X1 X2 : G, (M.op (M.op x (M.op x y)) X2) = (M.op (M.op X0 (M.op (M.op x (M.op x y)) X1)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq2065 eq51345
    | exact resolve eq51345 eq2065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51345
  have eq52613 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) X2) = (M.op (M.op x (M.op x y)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq570 X0 X1 X2 x x
       have i₂ := eq23374 X2 x x
       grind)
    | exact superpose eq23374 eq570
    | exact resolve eq570 eq23374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570 eq23374
  have eq52636 : ∀ X0 X1 X2 : G, (M.op (M.op x (M.op x y)) X2) = (M.op (M.op X1 (M.op X0 (M.op (M.op x y) x))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52613 X1 (M.op X1 (M.op X0 x)) X2
       have i₂ := eq410 X0 X1
       grind)
    | exact superpose eq410 eq52613
    | exact resolve eq52613 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq54167 : ∀ X2 X3 X4 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X2 X4) (M.op (M.op x (M.op x y)) X2)) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq623 x x X2 X3 X4
       have i₂ := eq45025 X2 x x
       grind)
    | exact superpose eq45025 eq623
    | exact resolve eq623 eq45025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq54949 : ∀ X0 : G, (M.op (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) (M.op (M.op (M.op x (M.op x y)) X0) (M.op x (M.op x y)))) = (k (M.op (M.op (M.op x (M.op x y)) X0) (M.op x (M.op x y))) (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    intro X0
    grind
  clear eq54167
  have eq55111 : ∀ X0 : G, (M.op (M.op x (M.op x y)) (M.op (M.op (M.op x (M.op x y)) X0) (M.op x (M.op x y)))) = (k (M.op (M.op (M.op x (M.op x y)) X0) (M.op x (M.op x y))) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq3426 eq54949
    | exact resolve eq54949 eq3426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54949
  have eq55601 : (M.op (M.op x (M.op x y)) (M.op (M.op (M.op x y) x) (M.op x (M.op x y)))) = (k (M.op (M.op (M.op x y) x) (M.op x (M.op x y))) (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq55111 x
       have i₂ := eq348 (M.op x sF0) x
       grind)
    | exact superpose eq348 eq55111
    | exact resolve eq55111 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55111
  have eq55799 : (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) = (k (M.op x (M.op x y)) (M.op x (M.op x y))) := by
    first
    | exact superpose eq1615 eq55601
    | exact resolve eq55601 eq1615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1615 eq55601
  have eq55909 : (M.op x (M.op x y)) = (k (M.op x (M.op x y)) (M.op x (M.op x y))) := by
    first
    | exact superpose eq3426 eq55799
    | exact resolve eq55799 eq3426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3426 eq55799
  have eq61364 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (M.op x y) x) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq323 X0
       have i₂ := eq209 (τ X0) (τ X0)
       grind)
    | exact superpose eq209 eq323
    | exact resolve eq323 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq61365 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op x (M.op x y)) (τ X0))) := by
    intro X0
    first
    | exact superpose eq2065 eq61364
    | exact resolve eq61364 eq2065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61364
  have eq79344 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq189 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq189
    | (have j0 := eq189 y
       grind)
    | exact resolve eq189 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq79440 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq79344
  have eq79493 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq79440
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq79440
    | exact resolve eq79440 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq79440
  have eq79853 : ∀ X0 : G, (σ (M.op (M.op x (M.op x y)) (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq61365 X0
       have i₂ := eq231 (τ X0) X0
       grind)
    | exact superpose eq231 eq61365
    | (have j1 := eq231 (τ X0) X0
       grind)
    | exact resolve eq61365 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231 eq61365
  have eq79878 : ∀ X0 : G, (σ (M.op (M.op x (M.op x y)) (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq79853 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79853
  have eq79882 : ∀ X0 : G, (k (k X0 X0) X0) = (σ (M.op (M.op x (M.op x y)) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq79878 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq79878
    | (have j0 := eq79878 X0
       grind)
    | exact resolve eq79878 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79878
  have eq113057 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op x (M.op x y)) (M.op (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq662 X0 X1
       have i₂ := eq25791 (M.op X0 (M.op X0 X0)) X0 X1
       grind)
    | exact superpose eq25791 eq662
    | exact resolve eq662 eq25791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq113058 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op x (M.op x y)) (M.op (M.op x (M.op x y)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq113057 X1 X1
       have i₂ := eq25791 (M.op x sF0) X1 (M.op X1 X1)
       grind)
    | exact superpose eq25791 eq113057
    | exact resolve eq113057 eq25791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25791 eq113057
  have eq113059 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) x) X0) = (k (M.op (M.op X0 X1) X0) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq113058 X1 X1
       have i₂ := eq209 (M.op x sF0) X1
       grind)
    | exact superpose eq209 eq113058
    | exact resolve eq113058 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113058
  have eq113060 : ∀ X0 X1 : G, (M.op (M.op x (M.op x y)) X0) = (k (M.op (M.op X0 X1) X0) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | exact superpose eq2065 eq113059
    | exact resolve eq113059 eq2065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113059
  have eq113450 : ∀ X0 : G, (M.op (M.op x (M.op x y)) (σ y)) = (k (M.op (M.op (σ y) X0) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq418 eq113060
    | exact resolve eq113060 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113060
  have eq113504 : (M.op (M.op x (M.op x y)) (σ y)) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq693 eq113450
    | exact resolve eq113450 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693 eq113450
  have eq113870 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1235 eq113504
    | exact resolve eq113504 eq1235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1235 eq113504
  have eq121083 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op (M.op X1 X2) X1))) = (M.op (M.op (M.op x y) x) (M.op X3 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq782 X0 X1 X2 X3 x
       have i₂ := eq348 (M.op X3 (M.op X0 X1)) x
       grind)
    | exact superpose eq348 eq782
    | exact resolve eq782 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq121084 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op (M.op X1 X2) X1))) = (M.op (M.op x (M.op x y)) (M.op X3 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq2065 eq121083
    | exact resolve eq121083 eq2065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121083
  have eq147644 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X2) X1))) = (M.op (M.op (M.op x y) x) (M.op (M.op (M.op X3 X4) X3) X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq786 X0 X1 X2 X3 X4 x
       have i₂ := eq348 (M.op (M.op (M.op X3 X4) X3) X1) x
       grind)
    | exact superpose eq348 eq786
    | exact resolve eq786 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348 eq786
  have eq147645 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X2) X1))) = (M.op (M.op x (M.op x y)) (M.op (M.op (M.op X3 X4) X3) X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq2065 eq147644
    | exact resolve eq147644 eq2065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147644
  have eq147646 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X2) X1))) = (M.op (M.op x (M.op x y)) (M.op (M.op x (M.op x y)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq147645 X0 X1 X2 x x
       have i₂ := eq45025 X1 x x
       grind)
    | exact superpose eq45025 eq147645
    | exact resolve eq147645 eq45025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147645
  have eq147647 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) x) X1) = (M.op X0 (M.op X0 (M.op (M.op X1 X2) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq147646 X0 X1 X2
       have i₂ := eq209 (M.op x sF0) X1
       grind)
    | exact superpose eq209 eq147646
    | exact resolve eq147646 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147646
  have eq147648 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X2) X1))) = (M.op (M.op x (M.op x y)) X1) := by
    intro X0 X1 X2
    first
    | exact superpose eq2065 eq147647
    | exact resolve eq147647 eq2065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147647
  have eq185141 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X0 (M.op (M.op X1 X2) X1))) (M.op (M.op X1 X2) X1)) = (M.op (M.op x (M.op x y)) (M.op (M.op (M.op X1 X2) X1) (M.op (M.op X1 X2) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq527 X0 X1 X2
       have i₂ := eq36414 X0 (M.op (M.op X1 X2) X1) (M.op (M.op X1 X2) X1)
       grind)
    | exact superpose eq36414 eq527
    | exact resolve eq527 eq36414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527 eq36414
  have eq185142 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X0 (M.op (M.op X1 X2) X1))) (M.op (M.op X1 X2) X1)) = (M.op (M.op x (M.op x y)) (M.op (M.op x (M.op x y)) (M.op (M.op (M.op X1 X2) X1) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq185141 X0 X1 X2
       have i₂ := eq121084 (M.op (M.op X1 X2) X1) X1 X2 (M.op x sF0)
       grind)
    | exact superpose eq121084 eq185141
    | exact resolve eq185141 eq121084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121084 eq185141
  have eq185143 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X0 (M.op (M.op X1 X2) X1))) (M.op (M.op X1 X2) X1)) = (M.op (M.op (M.op x y) x) (M.op (M.op (M.op X1 X2) X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq185142 X0 X1 X2
       have i₂ := eq209 (M.op x sF0) (M.op (M.op (M.op X1 X2) X1) X1)
       grind)
    | exact superpose eq209 eq185142
    | exact resolve eq185142 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185142
  have eq185144 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X0 (M.op (M.op X1 X2) X1))) (M.op (M.op X1 X2) X1)) = (M.op (M.op x (M.op x y)) (M.op (M.op (M.op X1 X2) X1) X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq2065 eq185143
    | exact resolve eq185143 eq2065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185143
  have eq185145 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X0 (M.op (M.op X1 X2) X1))) (M.op (M.op X1 X2) X1)) = (M.op (M.op x (M.op x y)) (M.op (M.op x (M.op x y)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq185144 X0 X1 X2
       have i₂ := eq45025 X1 X1 X2
       grind)
    | exact superpose eq45025 eq185144
    | exact resolve eq185144 eq45025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185144
  have eq185146 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) x) X1) = (k (M.op X0 (M.op X0 (M.op (M.op X1 X2) X1))) (M.op (M.op X1 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq185145 X0 X1 X2
       have i₂ := eq209 (M.op x sF0) X1
       grind)
    | exact superpose eq209 eq185145
    | exact resolve eq185145 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq185145
  have eq185147 : ∀ X1 X2 : G, (M.op (M.op (M.op x y) x) X1) = (k (M.op (M.op x (M.op x y)) X1) (M.op (M.op X1 X2) X1)) := by
    intro X1 X2
    first
    | (have i₁ := eq185146 x X1 X2
       have i₂ := eq147648 x X1 X2
       grind)
    | exact superpose eq147648 eq185146
    | exact resolve eq185146 eq147648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147648 eq185146
  have eq185148 : ∀ X1 X2 : G, (M.op (M.op x (M.op x y)) X1) = (k (M.op (M.op x (M.op x y)) X1) (M.op (M.op X1 X2) X1)) := by
    intro X1 X2
    first
    | exact superpose eq2065 eq185147
    | exact resolve eq185147 eq2065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2065 eq185147
  have eq185613 : (σ (M.op (M.op x (M.op x y)) x)) ≠ (σ (M.op (M.op x (M.op x y)) x)) ∨ (σ (M.op (M.op x (M.op x y)) x)) = (M.op (σ (M.op (M.op x (M.op x y)) x)) (σ (M.op (M.op x (M.op x y)) x))) := by
    first
    | exact superpose eq185148 eq1132
    | (have j0 := eq1132 (M.op (M.op x (M.op x y)) x)
       grind)
    | exact resolve eq1132 eq185148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185148
  have eq185617 : (σ (M.op (M.op x (M.op x y)) x)) = (M.op (σ (M.op (M.op x (M.op x y)) x)) (σ (M.op (M.op x (M.op x y)) x))) := by grind
  clear eq185613
  have eq185620 : (σ (M.op (M.op x y) x)) = (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) := by
    first
    | (have i₁ := eq185617
       have i₂ := eq207 sF0
       grind)
    | exact superpose eq207 eq185617
    | exact resolve eq185617 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq185617
  have eq241541 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) (σ y)) := by
    first
    | exact superpose eq185620 eq5545
    | exact resolve eq5545 eq185620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241629 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op (M.op x y) x)) (σ y)) := by
    first
    | exact superpose eq185620 eq241541
    | exact resolve eq241541 eq185620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185620 eq241541
  have eq247131 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq111 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247142 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq247131
    | exact resolve eq247131 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247131
  have eq247153 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq247142
       have r₂ := eq28
       grind)
    | exact resolve eq247142 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247142
  have eq247166 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq247153
  have eq247374 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq247166
    | exact resolve eq247166 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247166
  have eq247457 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq247374 eq111
    | exact resolve eq111 eq247374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq247374
  have eq247475 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq247457
  have eq247479 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq247475
       have r₂ := eq28
       grind)
    | exact resolve eq247475 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247475
  have eq247492 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by grind
  have eq248037 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq247492 eq50
    | exact resolve eq50 eq247492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247492
  have eq248364 : (τ (σ x)) = (k x x) ∨ y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq247479 eq248037
    | exact resolve eq248037 eq247479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247479 eq248037
  have eq248414 : (τ (σ x)) = (k x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq248364
  have eq248422 : x = (k x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq248414
    | exact resolve eq248414 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq248414
  have eq248424 : y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq32159 x
       grind)
    | (have r₁ := eq248422
       have r₂ := eq32159 x
       grind)
    | exact resolve eq248422 eq32159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32159 eq248422
  have eq248425 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq109
       have i₂ := eq248424
       grind)
    | exact superpose eq248424 eq109
    | exact resolve eq109 eq248424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq248436 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by grind
  have eq248551 : x ≠ y ∨ x = (M.op x x) := by grind
  clear eq248424
  have eq248639 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq248436
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq248436
    | exact resolve eq248436 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248436
  have eq248645 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq248425
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq248425
    | exact resolve eq248425 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248425
  have eq248716 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq248639
       grind)
    | exact superpose eq248639 eq74
    | exact resolve eq74 eq248639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248639
  have eq248754 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq248716
    | exact resolve eq248716 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248716
  have eq260601 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq248645
       have r₂ := eq248551
       grind)
    | exact resolve eq248645 eq248551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248551 eq248645
  have eq260608 : (τ (σ y)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq260601 eq50
    | exact resolve eq50 eq260601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq260654 : y = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq260608
    | exact resolve eq260608 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260608
  have eq260669 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1136 x
       have i₂ := eq260654
       grind)
    | exact superpose eq260654 eq1136
    | (have j0 := eq1136 x
       grind)
    | exact resolve eq1136 eq260654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136 eq260654
  have eq260706 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq260669
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq260669
    | exact resolve eq260669 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq260669
  have eq260726 : (k (σ y) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq260706
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq260706
    | exact resolve eq260706 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260706
  have eq260737 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq260726
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq260726
    | exact resolve eq260726 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260726
  have eq260746 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq260737
    | exact resolve eq260737 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260737
  have eq260751 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq260746
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq260746
    | exact resolve eq260746 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260746
  have eq702714 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq260751 eq248754
    | exact resolve eq248754 eq260751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260751
  have eq702742 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq702714
  have eq702755 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq702742
       have r₂ := eq28
       grind)
    | exact resolve eq702742 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702742
  have eq702770 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq702755
  have eq703477 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq702770 eq260601
    | exact resolve eq260601 eq702770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260601 eq702770
  have eq703511 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq703477
  have eq703535 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq703511
  have eq703804 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq703535
    | exact resolve eq703535 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703535
  have eq704880 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq703804 eq248754
    | exact resolve eq248754 eq703804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248754 eq703804
  have eq704907 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq704880
  have eq704919 : x = (M.op x x) := by
    first
    | (have r₁ := eq704907
       have r₂ := eq28
       grind)
    | exact resolve eq704907 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704907
  have eq704925 : (M.op (M.op x y) x) = (M.op x x) := by
    first
    | (have i₁ := eq56 x
       have i₂ := eq704919
       grind)
    | exact superpose eq704919 eq56
    | exact resolve eq56 eq704919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq705008 : (M.op x (M.op x y)) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq5543 x x
       have i₂ := eq704919
       grind)
    | exact superpose eq704919 eq5543
    | exact resolve eq5543 eq704919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5543
  have eq705137 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq705008
       have i₂ := eq704919
       grind)
    | exact superpose eq704919 eq705008
    | exact resolve eq705008 eq704919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705008
  have eq705212 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq704925
       have i₂ := eq704919
       grind)
    | exact superpose eq704919 eq704925
    | exact resolve eq704925 eq704919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704919 eq704925
  have eq705247 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq705137
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq705137
    | exact resolve eq705137 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705137
  have eq705433 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq705212 eq241629
    | exact resolve eq241629 eq705212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241629
  have eq705742 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq705433
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq705433
    | exact resolve eq705433 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq705433
  have eq705782 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq705742
    | exact resolve eq705742 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq705742
  have eq705844 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq705247 eq55909
    | exact resolve eq55909 eq705247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55909
  have eq707190 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) x)) := by
    first
    | exact superpose eq705782 eq1688
    | exact resolve eq1688 eq705782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1688
  have eq707204 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq705782 eq113870
    | exact resolve eq113870 eq705782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113870
  have eq707469 : x = (M.op (M.op (σ x) (σ y)) x) := by
    first
    | exact superpose eq705212 eq707190
    | exact resolve eq707190 eq705212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707190
  have eq708413 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq705844 eq129
    | exact resolve eq129 eq705844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq708487 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq705844 eq1132
    | (have j0 := eq1132 (M.op x y)
       grind)
    | exact resolve eq1132 eq705844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705844
  have eq708508 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq708487
  have eq708522 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq708508
    | exact resolve eq708508 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708508
  have eq708532 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq708413
    | exact resolve eq708413 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708413
  have eq710780 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) x) (σ y)) := by
    first
    | exact superpose eq707469 eq5545
    | exact resolve eq5545 eq707469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq710912 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op x (σ y)) := by
    first
    | exact superpose eq707469 eq710780
    | exact resolve eq710780 eq707469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707469 eq710780
  have eq711018 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq705782 eq710912
    | exact resolve eq710912 eq705782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710912
  have eq712175 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq708522 eq58
    | exact resolve eq58 eq708522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq712278 : ∀ X0 : G, (M.op (M.op x (M.op x y)) X0) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq708522 eq52613
    | exact resolve eq52613 eq708522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq712332 : ∀ X0 : G, (M.op (M.op x (M.op x y)) X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq708522 eq712278
    | exact resolve eq712278 eq708522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712278
  have eq712432 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq708522 eq712175
    | exact resolve eq712175 eq708522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708522 eq712175
  have eq712459 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq705247 eq712332
    | exact resolve eq712332 eq705247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712332
  have eq712609 : (σ (σ (M.op x y))) ≠ (σ (σ (M.op x y))) ∨ (σ (σ (M.op x y))) = (M.op (σ (σ (M.op x y))) (σ (σ (M.op x y)))) := by
    first
    | exact superpose eq708532 eq1132
    | (have j0 := eq1132 (σ (M.op x y))
       grind)
    | exact resolve eq1132 eq708532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132 eq708532
  have eq712630 : (σ (σ (M.op x y))) = (M.op (σ (σ (M.op x y))) (σ (σ (M.op x y)))) := by grind
  clear eq712609
  have eq716894 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X0 (M.op (M.op x y) X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq705247 eq51287
    | exact resolve eq51287 eq705247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51287
  have eq724334 : ∀ X0 X1 X2 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op X0 (M.op (M.op x y) X1)) X2) x) := by
    intro X0 X1 X2
    first
    | exact superpose eq705247 eq51378
    | exact resolve eq51378 eq705247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51378
  have eq724335 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op X0 (M.op (M.op x y) X1)) X2) x) := by
    intro X0 X1 X2
    first
    | exact superpose eq705212 eq724334
    | exact resolve eq724334 eq705212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724334
  have eq725198 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op x X0) := by
    intro X0 X1
    first
    | exact superpose eq724335 eq519
    | exact resolve eq519 eq724335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq725404 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x (M.op x y)) X3) = (M.op (M.op (M.op (M.op X0 (M.op (M.op x y) X1)) X2) x) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq724335 eq52613
    | exact resolve eq52613 eq724335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52613
  have eq725462 : ∀ X3 : G, (M.op x X3) = (M.op (M.op x (M.op x y)) X3) := by
    intro X3
    first
    | exact superpose eq724335 eq725404
    | exact resolve eq725404 eq724335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724335 eq725404
  have eq726066 : ∀ X3 : G, (M.op x X3) = (M.op (M.op x y) X3) := by
    intro X3
    first
    | exact superpose eq705247 eq725462
    | exact resolve eq725462 eq705247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725462
  have eq730462 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X2) = (M.op (M.op X0 (M.op (M.op x y) X1)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq705247 eq51885
    | exact resolve eq51885 eq705247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51885
  have eq776609 : ∀ X0 X1 X2 : G, (M.op (M.op x (M.op x y)) X2) = (M.op (M.op X1 (M.op X0 x)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq705212 eq52636
    | exact resolve eq52636 eq705212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52636 eq705212
  have eq776610 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X2) = (M.op (M.op X1 (M.op X0 x)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq705247 eq776609
    | exact resolve eq776609 eq705247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776609
  have eq776611 : ∀ X0 X1 X2 : G, (M.op x X2) = (M.op (M.op X1 (M.op X0 x)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq726066 eq776610
    | exact resolve eq776610 eq726066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776610
  have eq777485 : ∀ X0 X2 : G, (M.op (M.op x (M.op x y)) X2) = (M.op (M.op x X0) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq45025 X2 X0 (M.op x x)
       have i₂ := eq776611 x X0 X0
       grind)
    | exact superpose eq776611 eq45025
    | exact resolve eq45025 eq776611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45025 eq776611
  have eq778868 : ∀ X0 X2 : G, (M.op (M.op x y) X2) = (M.op (M.op x X0) X2) := by
    intro X0 X2
    first
    | exact superpose eq705247 eq777485
    | exact resolve eq777485 eq705247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705247 eq777485
  have eq779384 : ∀ X0 X2 : G, (M.op x X2) = (M.op (M.op x X0) X2) := by
    intro X0 X2
    first
    | exact superpose eq726066 eq778868
    | exact resolve eq778868 eq726066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778868
  have eq796945 : ∀ X0 : G, (M.op x X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq726066 eq712459
    | exact resolve eq712459 eq726066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712459
  have eq801835 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ (M.op x y)))) = (M.op (M.op x X0) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq796945 eq14
    | exact resolve eq14 eq796945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796945
  have eq802740 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op x X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq712432 eq801835
    | exact resolve eq801835 eq712432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712432 eq801835
  have eq820433 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ (σ (M.op x y))) (σ (σ (M.op x y)))) (σ y)) := by
    first
    | exact superpose eq712630 eq5545
    | exact resolve eq5545 eq712630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5545
  have eq820504 : ∀ X0 X1 : G, (M.op (σ (σ (M.op x y))) (σ (σ (M.op x y)))) = (M.op (M.op X0 (M.op (M.op x y) X1)) (σ (σ (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq712630 eq716894
    | exact resolve eq716894 eq712630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716894
  have eq820507 : (M.op (σ (σ (M.op x y))) (σ (σ (M.op x y)))) = (M.op (M.op x y) (σ (σ (M.op x y)))) := by
    first
    | exact superpose eq730462 eq820504
    | exact resolve eq820504 eq730462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730462 eq820504
  have eq820570 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq712630 eq820433
    | exact resolve eq820433 eq712630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820433
  have eq820663 : (M.op (σ (σ (M.op x y))) (σ (σ (M.op x y)))) = (M.op x (σ (σ (M.op x y)))) := by
    first
    | exact superpose eq726066 eq820507
    | exact resolve eq820507 eq726066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726066 eq820507
  have eq820713 : (M.op (σ x) (σ y)) = (M.op (σ (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq705782 eq820570
    | exact resolve eq820570 eq705782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820570
  have eq820776 : (σ (σ (M.op x y))) = (M.op x (σ (σ (M.op x y)))) := by
    first
    | exact superpose eq712630 eq820663
    | exact resolve eq820663 eq712630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712630 eq820663
  have eq824231 : (σ (M.op x y)) = (M.op (σ (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq820776 eq802740
    | exact resolve eq802740 eq820776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802740 eq820776
  have eq3063461 : ∀ X0 : G, (k (k X0 X0) X0) = (σ (M.op x (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq79882 X0
       have i₂ := eq779384 sF0 (τ X0)
       grind)
    | exact superpose eq779384 eq79882
    | (have j0 := eq79882 X0
       grind)
    | exact resolve eq79882 eq779384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79882 eq779384
  have eq3063561 : (k (M.op (σ y) (σ y)) (σ y)) = (σ (M.op x (τ (σ y)))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq79493 eq3063461
    | (have j0 := eq3063461 (σ y)
       grind)
    | exact resolve eq3063461 eq79493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79493 eq3063461
  have eq3064407 : (σ (M.op x y)) = (k (M.op (σ y) (σ y)) (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq30 eq3063561
    | exact resolve eq3063561 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3063561
  have eq3064779 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3064407
  have eq3065038 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq418 eq3064779
    | exact resolve eq3064779 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418 eq3064779
  have eq3065192 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq705782 eq3065038
    | exact resolve eq3065038 eq705782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705782 eq3065038
  have eq3065273 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3065192
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3065192
    | exact resolve eq3065192 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3065192
  have eq3065308 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq21 eq3065273
    | exact resolve eq3065273 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3065273
  have eq3065319 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq3065308
       have r₂ := eq28
       grind)
    | exact resolve eq3065308 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3065308
  have eq3065324 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq3065319
    | exact resolve eq3065319 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3065319
  have eq3065486 : (M.op (σ y) (σ y)) = (M.op x (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3065324 eq725198
    | exact resolve eq725198 eq3065324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3065492 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq711018 eq3065486
    | exact resolve eq3065486 eq711018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711018 eq3065486
  have eq3065807 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3065492 eq3065324
    | exact resolve eq3065324 eq3065492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3065324 eq3065492
  have eq3065975 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3065807
  have eq3066522 : (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq725198 y y
       have i₂ := eq3065975
       grind)
    | exact superpose eq3065975 eq725198
    | exact resolve eq725198 eq3065975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3066530 : (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3066522
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3066522
    | exact resolve eq3066522 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3066522
  have eq3067709 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3065975
       have i₂ := eq3066530
       grind)
    | exact superpose eq3066530 eq3065975
    | exact resolve eq3065975 eq3066530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3065975 eq3066530
  have eq3067873 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3067709
  have eq3068358 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3067873 eq707204
    | exact resolve eq707204 eq3067873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707204 eq3067873
  have eq3070665 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3068358 eq86
    | exact resolve eq86 eq3068358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq3068358
  have eq3070744 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq3070665
    | exact resolve eq3070665 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3070665
  have eq3074075 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq3070744
       grind)
    | exact superpose eq3070744 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq3070744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3070744
  have eq3074096 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq3074075
  have eq3074337 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq725198 y y
       have i₂ := eq3074096
       grind)
    | exact superpose eq3074096 eq725198
    | exact resolve eq725198 eq3074096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725198
  have eq3074345 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3074337
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3074337
    | exact resolve eq3074337 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3074337
  have eq3076234 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3074096
       have i₂ := eq3074345
       grind)
    | exact superpose eq3074345 eq3074096
    | exact resolve eq3074096 eq3074345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3074096 eq3074345
  have eq3076399 : y = (M.op x y) := by grind
  clear eq3076234
  have eq3076787 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq3076399 eq21
    | exact resolve eq21 eq3076399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq3076399
  have eq3078722 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq3076787
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq3076787
    | exact resolve eq3076787 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq3076787
  have eq3079060 : (M.op (σ x) (σ y)) = (M.op (σ (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq3078722 eq820713
    | exact resolve eq820713 eq3078722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820713 eq3078722
  have eq3079522 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq824231 eq3079060
    | exact resolve eq3079060 eq824231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824231 eq3079060
  have eq3079735 : False := by grind
  exact eq3079735

/-- `Equation4417`: `x ◇ (x ◇ y) = (z ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxx_y_pxy_Equation4417 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4417 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4417.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X0) X2) := by
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
  have eq30 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq25
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq25
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
  have eq51 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X1) X3) = (M.op X1 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 X1 (M.op X1 x) X3
       have i₂ := eq14 X1 x X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X0)) X3) = (M.op (M.op X2 X0) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 X0) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X3 X1) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 X1 x X3
       have i₂ := eq14 X1 x X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op X0 X1) X0) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X2) X3 X1
       have i₂ := eq14 X1 X2 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3 (M.op X2 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq92
    | exact resolve eq92 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq207 : (M.op (M.op x y) x) = (M.op y (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq56 (M.op y x)
       have i₂ := eq56 x
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 y) X0) := by
    intro X0
    first
    | (have i₁ := eq56 x
       have i₂ := eq14 y x X0
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq57 eq57
    | exact resolve eq57 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq57 x
       have i₂ := eq14 sF3 x x
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq35
  have eq350 : (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) (M.op y y)) := by
    first
    | (have i₁ := eq209 (M.op y y)
       have i₂ := eq209 y
       grind)
    | exact superpose eq209 eq209
    | exact resolve eq209 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op (M.op X3 (M.op X1 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X1 (M.op X1 X2) X3
       have i₂ := eq14 X1 X2 X0
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) X3) = (M.op (M.op (M.op X0 X1) X0) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 (M.op X2 X1) X2 X3
       have i₂ := eq53 X2 X1 X0
       grind)
    | (have i₁ := eq53 (M.op X2 X1) X2 X3
       have i₂ := eq53 X0 X1 X2
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op y X0)) X1) = (M.op (M.op (M.op x y) x) y) := by
    intro X0 X1
    first
    | (have i₁ := eq53 y (M.op y X0) X1
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq364 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (σ y) X0)) X1) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq57 eq53
    | exact resolve eq53 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X0) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3 (M.op X2 X1)
       have i₂ := eq53 X2 X1 X0
       grind)
    | (have i₁ := eq14 X2 X3 (M.op X2 X1)
       have i₂ := eq53 X0 X1 X2
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X3) = (M.op (M.op X2 X1) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 X1) X2 X3
       have i₂ := eq53 X2 X1 X0
       grind)
    | (have i₁ := eq14 (M.op X2 X1) X2 X3
       have i₂ := eq53 X0 X1 X2
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq214 eq214
    | exact resolve eq214 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq413 : (M.op (M.op x y) x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op y (σ y))) := by
    first
    | exact superpose eq214 eq209
    | exact resolve eq209 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq422 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq58 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq58
    | (have j0 := eq58 x y X0
       grind)
    | exact resolve eq58 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq484 : ∀ X0 : G, (M.op (M.op X0 x) X0) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq422 x
       have i₂ := eq14 x x X0
       grind)
    | exact superpose eq14 eq422
    | (have j1 := eq14 x y X0
       grind)
    | exact resolve eq422 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq498 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X2 X1)) = (M.op X2 (M.op (M.op X3 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 X3 X2 (M.op X2 X1)
       have i₂ := eq53 X2 X1 X0
       grind)
    | (have i₁ := eq51 X3 X2 (M.op X2 X1)
       have i₂ := eq53 X0 X1 X2
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op (M.op X3 (M.op (M.op X2 X1) X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X1 (M.op (M.op X2 X1) X2) X3
       have i₂ := eq51 X2 X1 X0
       grind)
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq617 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x (M.op x y)) (M.op X0 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x y X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq55
    | (have j0 := eq55 x y X0 X1
       grind)
    | exact resolve eq55 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq816 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 x)) X0) = (M.op (M.op X1 x) (M.op x (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 x y X1 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq52
    | (have j0 := eq52 x y X1 X0
       grind)
    | exact resolve eq52 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq830 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 y)) X0) = (M.op (M.op X1 y) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 y x X1 X0
       have i₂ := eq56 x
       grind)
    | exact superpose eq56 eq52
    | exact resolve eq52 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq835 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X2 (M.op (M.op X1 (M.op X1 X3)) X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X1 X3 (M.op X1 (M.op X1 X3)) X2
       have i₂ := eq53 (M.op X1 (M.op X1 X3)) X1 X0
       grind)
    | (have i₁ := eq52 X1 X3 (M.op X1 (M.op X1 X3)) X2
       have i₂ := eq53 X0 X1 (M.op X1 (M.op X1 X3))
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq946 : ∀ X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) = (M.op (M.op (M.op X2 (σ y)) X2) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq57 eq54
    | exact resolve eq54 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq57
  have eq1042 : ∀ X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) := by
    intro X1
    first
    | exact superpose eq214 eq946
    | (have j0 := eq946 X1 (σ x)
       grind)
    | exact resolve eq946 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq1129 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq77 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq77 X1 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq13 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1149 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1129 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129
  have eq1151 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1149 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq1149 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq1149 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149
  have eq6512 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op x y) x)) X0) = (M.op (M.op (M.op X1 (M.op y y)) X1) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | exact superpose eq350 eq356
    | exact resolve eq356 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq6522 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) = (M.op (M.op (M.op X1 (M.op y (σ y))) X1) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | exact superpose eq413 eq356
    | exact resolve eq356 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq6523 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) = (M.op (M.op (M.op X1 (M.op (σ y) (σ y))) X1) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq402 eq356
    | exact resolve eq356 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356 eq402
  have eq6690 : ∀ X0 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq364 eq6523
    | exact resolve eq6523 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364 eq6523
  have eq6691 : ∀ X0 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) = (M.op (M.op (M.op (M.op x y) x) y) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq6522 X0 x
       have i₂ := eq361 sF3 x
       grind)
    | exact superpose eq361 eq6522
    | exact resolve eq6522 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6522
  have eq6695 : ∀ X0 : G, (M.op (M.op X0 (M.op (M.op x y) x)) X0) = (M.op (M.op (M.op (M.op x y) x) y) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq6512 X0 x
       have i₂ := eq361 y x
       grind)
    | exact superpose eq361 eq6512
    | exact resolve eq6512 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361 eq6512
  have eq6700 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) := by
    intro X0
    first
    | exact superpose eq214 eq6690
    | exact resolve eq6690 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq6690
  have eq6701 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) := by
    intro X0
    first
    | (have i₁ := eq6691 X0
       have i₂ := eq209 (M.op sF0 x)
       grind)
    | exact superpose eq209 eq6691
    | exact resolve eq6691 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6691
  have eq6705 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op (M.op x y) x)) X0) := by
    intro X0
    first
    | (have i₁ := eq6695 X0
       have i₂ := eq209 (M.op sF0 x)
       grind)
    | exact superpose eq209 eq6695
    | exact resolve eq6695 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq6695
  have eq6731 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq212 eq6700
    | exact resolve eq6700 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq6870 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq6700 eq6701
    | exact resolve eq6701 eq6700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6700 eq6701
  have eq6877 : (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) (σ y)) := by
    first
    | exact superpose eq6870 eq6731
    | exact resolve eq6731 eq6870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6731
  have eq7565 : (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq207 eq6705
    | exact resolve eq6705 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8162 : ∀ X0 X1 : G, (M.op y (M.op y X0)) = (M.op (M.op (M.op X1 (M.op (M.op x y) x)) X1) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | exact superpose eq207 eq385
    | exact resolve eq385 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq8388 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq6705 eq8162
    | exact resolve eq8162 eq6705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8162
  have eq8479 : (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq8388 x
       have i₂ := eq56 x
       grind)
    | exact superpose eq56 eq8388
    | exact resolve eq8388 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq8388
  have eq10525 : (M.op (M.op (M.op x y) x) y) = (M.op (M.op (M.op x y) x) (M.op x (M.op x y))) := by
    first
    | exact superpose eq207 eq816
    | exact resolve eq816 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq816
  have eq10652 : (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) (M.op x (M.op x y))) := by
    first
    | exact superpose eq7565 eq10525
    | exact resolve eq10525 eq7565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7565 eq10525
  have eq11317 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) = (M.op (M.op (M.op X0 x) X0) x) := by
    intro X0
    first
    | exact superpose eq10652 eq355
    | exact resolve eq355 eq10652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq11390 : (M.op (M.op x (M.op x y)) x) = (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq11317 x
       have i₂ := eq484 x
       grind)
    | exact superpose eq484 eq11317
    | exact resolve eq11317 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11317
  have eq11402 : (M.op (M.op x y) x) = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq8479 eq11390
    | exact resolve eq11390 eq8479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8479 eq11390
  have eq11406 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq11402
       have i₂ := eq53 x sF0 x
       grind)
    | (have i₁ := eq11402
       have i₂ := eq53 X0 sF0 x
       grind)
    | exact superpose eq53 eq11402
    | exact resolve eq11402 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11422 : (M.op x (M.op x y)) = (M.op (M.op (M.op x y) x) (M.op x (M.op x y))) := by
    first
    | exact superpose eq11402 eq484
    | exact resolve eq484 eq11402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484 eq11402
  have eq11477 : (M.op (M.op x y) x) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq10652 eq11422
    | exact resolve eq11422 eq10652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10652 eq11422
  have eq11565 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op X0 (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq11477 eq11406
    | exact resolve eq11406 eq11477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11406
  have eq12805 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) = (M.op (M.op x (M.op x y)) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) x)) := by
    first
    | (have i₁ := eq1042 x
       have i₂ := eq617 (M.op sF4 sF2) x
       grind)
    | exact superpose eq617 eq1042
    | exact resolve eq1042 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617 eq1042
  have eq12806 : (M.op (M.op x (M.op x y)) (M.op (M.op (M.op x y) x) x)) = (M.op (M.op (M.op x y) x) (σ y)) := by
    first
    | exact superpose eq6870 eq12805
    | exact resolve eq12805 eq6870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6870 eq12805
  have eq12807 : (M.op (M.op x y) x) = (M.op (M.op x (M.op x y)) (M.op (M.op (M.op x y) x) x)) := by
    first
    | exact superpose eq6877 eq12806
    | exact resolve eq12806 eq6877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6877 eq12806
  have eq12808 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (M.op (M.op x (M.op x y)) x)) := by
    first
    | exact superpose eq11477 eq12807
    | exact resolve eq12807 eq11477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12807
  have eq12809 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) := by
    first
    | exact superpose eq11565 eq12808
    | exact resolve eq12808 eq11565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11565 eq12808
  have eq12815 : ∀ X0 : G, (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq12809 eq13
    | (have j0 := eq13 X0 (M.op x (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (M.op x (M.op x y))
       have r₂ := eq12809
       grind)
    | exact resolve eq13 eq12809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12823 : ∀ X0 : G, (M.op (M.op X0 (M.op x (M.op x y))) X0) = (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq12809 eq53
    | exact resolve eq53 eq12809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq12853 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq12815 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12815
  have eq12872 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op X0 (M.op x (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq12809 eq12823
    | exact resolve eq12823 eq12809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12823
  have eq13522 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq12853 eq1151
    | (have j0 := eq1151 (M.op x (M.op x y)) X0
       grind)
    | exact resolve eq1151 eq12853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151
  have eq13537 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op x (M.op x y))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq12809 eq13522
    | (have j0 := eq13522 X0
       grind)
    | exact resolve eq13522 eq12809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13522
  have eq13538 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have j0 := eq13537 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13537
  have eq14746 : ∀ X0 X1 X2 : G, (M.op (M.op X0 y) (M.op (M.op x y) x)) = (M.op (M.op X1 (M.op (M.op (M.op X2 (M.op X0 y)) X2) (M.op X0 y))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq386 X2 (M.op X0 y) (M.op (M.op X2 (M.op X0 y)) X2) X1
       have i₂ := eq830 (M.op (M.op X2 (M.op X0 y)) X2) X0
       grind)
    | exact superpose eq830 eq386
    | exact resolve eq386 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq15072 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op (M.op x y) x)) = (M.op (M.op X1 (M.op (M.op (M.op X0 y) (M.op (M.op x y) x)) (M.op X0 y))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14746 X0 X1 x
       have i₂ := eq830 x X0
       grind)
    | exact superpose eq830 eq14746
    | exact resolve eq14746 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14746
  have eq15303 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op (M.op x y) x)) = (M.op (M.op X1 (M.op (M.op x y) x)) X1) := by
    intro X0 X1
    first
    | exact superpose eq6705 eq15072
    | exact resolve eq15072 eq6705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15072
  have eq15434 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 y) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq6705 eq15303
    | exact resolve eq15303 eq6705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6705 eq15303
  have eq15504 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op X0 y) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq11477 eq15434
    | exact resolve eq15434 eq11477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15434
  have eq22499 : ∀ X0 : G, (k (τ X0) (M.op x (M.op x y))) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq13538 eq303
    | exact resolve eq303 eq13538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq22504 : (M.op (σ x) (σ x)) = (σ (k x (M.op x (M.op x y)))) := by
    first
    | exact superpose eq13538 eq36
    | exact resolve eq36 eq13538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq22505 : (M.op (σ y) (σ y)) = (σ (k y (M.op x (M.op x y)))) := by
    first
    | exact superpose eq13538 eq37
    | exact resolve eq37 eq13538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq13538
  have eq22528 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq12853 eq22505
    | exact resolve eq22505 eq12853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22505
  have eq22529 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq12853 eq22504
    | exact resolve eq22504 eq12853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22504
  have eq22574 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq22528
       grind)
    | exact superpose eq22528 eq16
    | exact resolve eq16 eq22528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22528
  have eq22597 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq22529
       grind)
    | exact superpose eq22529 eq16
    | exact resolve eq16 eq22529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22529
  have eq34139 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X1) = (M.op (M.op X2 (M.op (M.op X0 y) (M.op (M.op x y) x))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq835 X1 X0 X2 y
       have i₂ := eq830 X0 X0
       grind)
    | exact superpose eq830 eq835
    | exact resolve eq835 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830 eq835
  have eq34666 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X1) = (M.op (M.op X2 (M.op (M.op X0 y) (M.op x (M.op x y)))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq11477 eq34139
    | exact resolve eq34139 eq11477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11477 eq34139
  have eq34840 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X1) = (M.op (M.op X2 (M.op x (M.op x y))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq15504 eq34666
    | exact resolve eq34666 eq15504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15504 eq34666
  have eq34943 : ∀ X0 X1 : G, (M.op x (M.op x y)) = (M.op (M.op X1 X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq12872 eq34840
    | exact resolve eq34840 eq12872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12872 eq34840
  have eq35078 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (k X0 (M.op x (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq34943 X0 X0
       have i₂ := eq12853 X0
       grind)
    | exact superpose eq12853 eq34943
    | exact resolve eq34943 eq12853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35206 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq34943 X0 x
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq34943
    | exact resolve eq34943 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35289 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq546 X0 X1 x x
       have i₂ := eq34943 (M.op (M.op x X1) x) x
       grind)
    | exact superpose eq34943 eq546
    | exact resolve eq546 eq34943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq35307 : ∀ X0 X2 : G, (M.op x (M.op x y)) = (M.op X0 (M.op (M.op X2 X0) X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq498 X0 x X0 X2
       have i₂ := eq34943 X0 (M.op X0 x)
       grind)
    | exact superpose eq34943 eq498
    | exact resolve eq498 eq34943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq35499 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq35307 X0 x
       have i₂ := eq34943 X0 x
       grind)
    | exact superpose eq34943 eq35307
    | exact resolve eq35307 eq34943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35307
  have eq35509 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) X1) := by
    intro X1
    first
    | (have i₁ := eq35289 x X1
       have i₂ := eq34943 X1 x
       grind)
    | exact superpose eq34943 eq35289
    | exact resolve eq35289 eq34943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35289
  have eq40097 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq12853 eq22499
    | exact resolve eq22499 eq12853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12853
  have eq40107 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | exact superpose eq22499 eq35078
    | exact resolve eq35078 eq22499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22499 eq35078
  have eq40205 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq40097 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq40097
    | exact resolve eq40097 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41185 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 (M.op (σ X0) (σ X0))
       have i₂ := eq40205 X0
       grind)
    | exact superpose eq40205 eq15
    | exact resolve eq15 eq40205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40205
  have eq41618 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq35206 (σ X0) (σ X0)
       have i₂ := eq41185 X0
       grind)
    | exact superpose eq41185 eq35206
    | exact resolve eq35206 eq41185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41185
  have eq44689 : (M.op x (M.op x y)) = (M.op (τ (M.op x (M.op x y))) (τ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq35509 eq40107
    | exact resolve eq40107 eq35509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35509 eq40107
  have eq44946 : (M.op x (M.op x y)) = (τ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq44689
       have i₂ := eq40097 (M.op x sF0)
       grind)
    | exact superpose eq40097 eq44689
    | exact resolve eq44689 eq40097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40097 eq44689
  have eq45044 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq12809 eq44946
    | exact resolve eq44946 eq12809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12809 eq44946
  have eq45110 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq45044 eq15
    | exact resolve eq15 eq45044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45044
  have eq74912 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq93 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq74919 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq74912
    | exact resolve eq74912 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74912
  have eq74930 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq74919
       have r₂ := eq28
       grind)
    | exact resolve eq74919 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74919
  have eq74935 : (τ (σ y)) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq74930 eq22574
    | exact resolve eq22574 eq74930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22574 eq74930
  have eq75073 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq74935
    | exact resolve eq74935 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74935
  have eq75074 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq75073
  have eq75124 : (τ (σ y)) = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq75074 eq22597
    | exact resolve eq22597 eq75074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22597 eq75074
  have eq75264 : y = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq75124
    | exact resolve eq75124 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq75124
  have eq75265 : y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq75264
  have eq75462 : (M.op y y) = (M.op x (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq34943 y y
       have i₂ := eq75265
       grind)
    | exact superpose eq75265 eq34943
    | exact resolve eq34943 eq75265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34943
  have eq75766 : y = (M.op x (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq75265
       have i₂ := eq75462
       grind)
    | exact superpose eq75462 eq75265
    | exact resolve eq75265 eq75462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75265 eq75462
  have eq75837 : y = (M.op x (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq75766
  have eq76075 : y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq75837 eq35206
    | exact resolve eq35206 eq75837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75837
  have eq76076 : y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq76075
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq76075
    | exact resolve eq76075 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76075
  have eq76217 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41618 x
       have i₂ := eq76076
       grind)
    | exact superpose eq76076 eq41618
    | exact resolve eq41618 eq76076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41618
  have eq76272 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35206 x x
       have i₂ := eq76076
       grind)
    | exact superpose eq76076 eq35206
    | exact resolve eq35206 eq76076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35206 eq76076
  have eq76273 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq76272
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq76272
    | exact resolve eq76272 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76272
  have eq76326 : (M.op x (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq76217
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq76217
    | exact resolve eq76217 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76217
  have eq76377 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq76326
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq76326
    | exact resolve eq76326 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq76326
  have eq76391 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq76377
    | exact resolve eq76377 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76377
  have eq76687 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq76273 eq45110
    | exact resolve eq45110 eq76273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76795 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq76687
    | exact resolve eq76687 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76687
  have eq77300 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq76391 eq76273
    | exact resolve eq76273 eq76391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76273 eq76391
  have eq77357 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq77300
  have eq77463 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq77357 eq28
    | exact resolve eq28 eq77357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77357
  have eq77498 : y = (M.op x y) := by
    first
    | (have r₁ := eq77463
       have r₂ := eq76795
       grind)
    | exact resolve eq77463 eq76795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76795 eq77463
  have eq77502 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq77498 eq21
    | exact resolve eq21 eq77498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77615 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq77498 eq35499
    | exact resolve eq35499 eq77498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35499
  have eq77633 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq77498 eq45110
    | exact resolve eq45110 eq77498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45110
  have eq77652 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq77633
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq77633
    | exact resolve eq77633 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77633
  have eq77669 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq77615 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq77615
    | (have j0 := eq77615 X0
       grind)
    | exact resolve eq77615 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq77615
  have eq77774 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq77502
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq77502
    | exact resolve eq77502 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq77502
  have eq77781 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq77652
    | exact resolve eq77652 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq77652
  have eq77791 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq77498 eq77669
    | exact resolve eq77669 eq77498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77669
  have eq77871 : y = (σ (M.op x y)) := by
    first
    | exact superpose eq77498 eq77781
    | exact resolve eq77781 eq77498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77498 eq77781
  have eq77951 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq77774 eq27
    | exact resolve eq27 eq77774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq77774
  have eq80314 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq77871 eq77951
    | exact resolve eq77951 eq77871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77951
  have eq80315 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq80314
       have i₂ := eq77791 sF2
       grind)
    | exact superpose eq77791 eq80314
    | exact resolve eq80314 eq77791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77791 eq80314
  have eq80323 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq80315 eq28
    | exact resolve eq28 eq80315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq80315
  have eq80364 : False := by grind
  exact eq80364

/-- `Equation4419`: `x ◇ (x ◇ y) = (z ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_y_pxy_Equation4419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X1) X0) := by
    intro X0 X1 X2
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X2) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 (M.op X2 X1) X3
       have i₂ := eq16 X2 X1 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X1 X3
       have i₂ := eq16 X2 X1 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X0)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X0 (M.op x X1)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq182 X0
       have i₂ := eq16 X0 X0 X0
       grind)
    | exact superpose eq16 eq182
    | exact resolve eq182 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq185 : (M.op (M.op x y) x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq180 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq180
    | (have j0 := eq180 x
       grind)
    | exact resolve eq180 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 y X1
       have i₂ := eq180 X0
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 y))) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 y) X0
       have i₂ := eq180 X0
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq181
    | (have j0 := eq181 (σ x)
       grind)
    | exact resolve eq181 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) X0) := by
    intro X0 X1
    first
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 (σ y)))) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op (M.op X0 y) X1)) = (M.op (M.op X2 X1) (M.op X0 y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 y) X1 X2
       have i₂ := eq187 (M.op (M.op X0 y) X1) X0
       grind)
    | (have i₁ := eq16 (M.op x y) X1 X2
       have i₂ := eq187 (M.op (M.op x y) X1) X1
       grind)
    | exact superpose eq187 eq16
    | exact resolve eq16 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op X0 y) (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq180 (M.op X0 y)
       have i₂ := eq187 y X0
       grind)
    | (have i₁ := eq180 (M.op x y)
       have i₂ := eq187 y x
       grind)
    | exact superpose eq187 eq180
    | exact resolve eq180 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 y)) = (M.op (M.op X0 y) (M.op (M.op x y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq181 (M.op x y)
       have i₂ := eq187 sF3 x
       grind)
    | (have i₁ := eq181 (M.op x y)
       have i₂ := eq187 sF3 x
       grind)
    | exact superpose eq187 eq181
    | exact resolve eq181 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 y)) = (M.op (M.op x y) (M.op (M.op x y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq212 x
       have i₂ := eq187 (M.op sF0 sF3) x
       grind)
    | (have i₁ := eq212 x
       have i₂ := eq187 (M.op sF0 sF3) x
       grind)
    | exact superpose eq187 eq212
    | exact resolve eq212 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq214 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq211 x
       have i₂ := eq187 (M.op sF0 y) x
       grind)
    | (have i₁ := eq211 x
       have i₂ := eq187 (M.op sF0 y) x
       grind)
    | exact superpose eq187 eq211
    | exact resolve eq211 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq217 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 y)) = (M.op (M.op x y) (M.op (M.op x y) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq208 X0 X1 X2
       have i₂ := eq187 X1 X0
       grind)
    | (have i₁ := eq208 x X0 X2
       have i₂ := eq187 X0 X1
       grind)
    | exact superpose eq187 eq208
    | exact resolve eq208 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq222 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 y)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq181 eq213
    | exact resolve eq213 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq223 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq214 X0
       have i₂ := eq180 sF0
       grind)
    | exact superpose eq180 eq214
    | exact resolve eq214 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq243 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ y)) X1)) = (M.op (M.op X2 X1) (M.op X0 (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq194 eq16
    | exact resolve eq16 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ y)) y)) := by
    intro X0
    first
    | exact superpose eq194 eq180
    | exact resolve eq180 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq194 eq181
    | exact resolve eq181 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq194 eq248
    | exact resolve eq248 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq252 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op x y) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq222 eq244
    | exact resolve eq244 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq253 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq194 eq243
    | exact resolve eq243 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq258 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq181 eq249
    | exact resolve eq249 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq358 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq222 eq180
    | exact resolve eq180 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq679 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 (σ y))) X2) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq258 eq177
    | exact resolve eq177 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq680 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq358 eq177
    | exact resolve eq177 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq718 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op (M.op X0 X1) y)) = (M.op (M.op x y) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180 (M.op X2 X1)
       have i₂ := eq177 X2 X1 y X0
       grind)
    | (have i₁ := eq180 (M.op X2 X1)
       have i₂ := eq177 X0 X1 y X2
       grind)
    | exact superpose eq177 eq180
    | exact resolve eq180 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq722 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op (M.op X0 X1) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 (M.op X0 X1)
       have i₂ := eq177 X0 X1 sF3 x
       grind)
    | (have i₁ := eq181 (M.op x X1)
       have i₂ := eq177 X0 X1 sF3 x
       grind)
    | exact superpose eq177 eq181
    | exact resolve eq181 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq723 : ∀ X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X1)) = (M.op (M.op (σ x) (σ y)) (M.op X2 X1)) := by
    intro X1 X2
    first
    | exact superpose eq253 eq722
    | exact resolve eq722 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq724 : ∀ X1 X2 : G, (M.op (M.op x y) (M.op (M.op x y) X1)) = (M.op (M.op x y) (M.op X2 X1)) := by
    intro X1 X2
    first
    | (have i₁ := eq718 x X1 X2
       have i₂ := eq217 (M.op x X1) X1 X2
       grind)
    | (have i₁ := eq718 x y x
       have i₂ := eq217 x y X2
       grind)
    | exact superpose eq217 eq718
    | exact resolve eq718 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq718
  have eq744 : ∀ X0 : G, (k (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) (M.op X0 (σ y))) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq194 eq183
    | exact resolve eq183 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq762 : ∀ X0 : G, (k (M.op (M.op X0 (σ y)) (M.op X0 (σ y))) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ y)) (M.op X0 (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq194 (M.op (M.op x sF3) (M.op x sF3)) x
       have i₂ := eq183 (M.op x sF3)
       grind)
    | exact superpose eq183 eq194
    | exact resolve eq194 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq763 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y)))) = (k (M.op (M.op X0 (σ y)) (M.op X0 (σ y))) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq723 eq762
    | exact resolve eq762 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq767 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y)))) = (k (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq194 eq744
    | exact resolve eq744 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq769 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y)))) = (k (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq253 eq763
    | exact resolve eq763 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253 eq763
  have eq773 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq258 eq767
    | exact resolve eq767 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq775 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y)))) = (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq181 eq769
    | exact resolve eq769 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq779 : ∀ X0 : G, (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 (σ y))) = (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq773 X0
       have i₂ := eq183 sF4
       grind)
    | exact superpose eq183 eq773
    | exact resolve eq773 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq781 : ∀ X0 : G, (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq195 eq775
    | exact resolve eq775 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq785 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq781 x
       have i₂ := eq16 sF4 x sF4
       grind)
    | exact superpose eq16 eq781
    | exact resolve eq781 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq789 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq779 eq785
    | exact resolve eq785 eq779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779 eq785
  have eq816 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq723 X0 (M.op x X1)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq723
    | exact resolve eq723 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq831 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X1 X0)) X2) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) X2) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq723 eq177
    | exact resolve eq177 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq832 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X2 X0))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) X1) := by
    intro X0 X1 X2
    first
    | exact superpose eq723 eq16
    | exact resolve eq16 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq833 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X2 X0))) = (M.op (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) X1) := by
    intro X0 X1 X2
    first
    | exact superpose eq789 eq832
    | exact resolve eq832 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq834 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X1 X0)) X2) = (M.op (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) X2) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq789 eq831
    | exact resolve eq831 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq836 : ∀ X0 X1 : G, (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq789 eq816
    | exact resolve eq816 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789 eq816
  have eq880 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq884 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq978 : y ≠ (M.op x y) ∨ x = (M.op y y) ∨ y = (k x y) := by
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
  have eq982 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1010 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq880
       grind)
    | exact superpose eq880 eq41
    | exact resolve eq41 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq880
  have eq1011 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1010
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1010
    | exact resolve eq1010 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010
  have eq1013 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq1011
    | exact resolve eq1011 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq1021 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1013 eq884
    | exact resolve eq884 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1028 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1021
       have r₂ := eq27
       grind)
    | exact resolve eq1021 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq1032 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1028 eq27
    | exact resolve eq27 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1033 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1028 eq192
    | exact resolve eq192 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq1040 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1033
    | exact resolve eq1033 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033
  have eq1041 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1028 eq1040
    | exact resolve eq1040 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040
  have eq2947 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 (M.op X1 X2) X1
       have i₂ := eq179 X1 X2 X0
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2961 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op y (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq222 (M.op X0 (M.op X0 x))
       have i₂ := eq179 X0 x y
       grind)
    | exact superpose eq179 eq222
    | exact resolve eq222 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq2983 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq836 eq2961
    | exact resolve eq2961 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836 eq2961
  have eq3067 : (M.op (M.op x y) (M.op (σ x) (σ y))) = (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq358 eq2983
    | exact resolve eq2983 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2983
  have eq4774 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1028 eq982
    | (have r₁ := eq982
       have r₂ := eq1028
       grind)
    | exact resolve eq982 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982 eq1028
  have eq4775 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4774
  have eq4776 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1013 eq4775
    | exact resolve eq4775 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4775
  have eq4777 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq4776
       have r₂ := eq1032
       grind)
    | exact resolve eq4776 eq1032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4776
  have eq4795 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4777 eq183
    | exact resolve eq183 eq4777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4777
  have eq4829 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1013 eq4795
    | exact resolve eq4795 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013 eq4795
  have eq4845 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1041 eq4829
    | exact resolve eq4829 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041 eq4829
  have eq4856 : y = (M.op x y) := by
    first
    | (have r₁ := eq4845
       have r₂ := eq1032
       grind)
    | exact resolve eq4845 eq1032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032 eq4845
  have eq4862 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4856
       grind)
    | exact superpose eq4856 eq18
    | exact resolve eq18 eq4856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4863 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq4856
       grind)
    | exact superpose eq4856 eq24
    | exact resolve eq24 eq4856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq4867 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 (M.op x y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq187 X0 X1
       have i₂ := eq4856
       grind)
    | exact superpose eq4856 eq187
    | exact resolve eq187 eq4856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4872 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | (have i₁ := eq978
       have i₂ := eq4856
       grind)
    | exact superpose eq4856 eq978
    | (have r₁ := eq978
       have r₂ := eq4856
       grind)
    | exact resolve eq978 eq4856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978 eq4856
  have eq4873 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq4872
  have eq4876 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4863 eq20
    | exact resolve eq20 eq4863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5013 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = (M.op X0 (M.op (M.op X1 y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq223 eq175
    | exact resolve eq175 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5016 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) X0) = (M.op X0 (M.op (M.op X1 (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq252 eq175
    | exact resolve eq175 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5030 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) = (M.op X0 (M.op (M.op X1 (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq258 eq175
    | exact resolve eq175 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq5084 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op (M.op (M.op X5 X3) (M.op X1 X2)) X2)) (M.op (M.op X5 X3) (M.op X1 X2))) = (M.op (M.op (M.op X5 X3) (M.op X1 X2)) (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq175 X1 X2 (M.op (M.op X5 X3) (M.op X1 X2)) X4
       have i₂ := eq175 X5 X3 (M.op X1 X2) X0
       grind)
    | exact superpose eq175 eq175
    | exact resolve eq175 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5120 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X0)) X4) = (M.op (M.op X3 X0) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq177 X3 X0 X4 (M.op x (M.op X0 X2))
       have i₂ := eq175 X1 X2 X0 x
       grind)
    | exact superpose eq175 eq177
    | exact resolve eq177 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5130 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op y (M.op (M.op X0 X1) y))) := by
    intro X0 X1
    first
    | (have i₁ := eq223 (M.op x (M.op y X1))
       have i₂ := eq175 X0 X1 y x
       grind)
    | exact superpose eq175 eq223
    | exact resolve eq223 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq5144 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op x y) (M.op (σ y) (M.op (M.op X0 X1) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq252 (M.op x (M.op sF3 X1))
       have i₂ := eq175 X0 X1 sF3 x
       grind)
    | exact superpose eq175 eq252
    | exact resolve eq252 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq5145 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) X2) = (M.op (M.op (σ y) (M.op (M.op X0 X1) (σ y))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq194 X0 (M.op x (M.op sF3 X1))
       have i₂ := eq175 X0 X1 sF3 x
       grind)
    | exact superpose eq175 eq194
    | exact resolve eq194 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq5201 : ∀ X2 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X2) = (M.op (M.op (σ x) (σ y)) X2) := by
    intro X2
    first
    | exact superpose eq679 eq5145
    | exact resolve eq5145 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679 eq5145
  have eq5202 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X0 X1) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq724 eq5144
    | exact resolve eq5144 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5144
  have eq5207 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X0 X1) y))) := by
    intro X0 X1
    first
    | exact superpose eq724 eq5130
    | exact resolve eq5130 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724 eq5130
  have eq5212 : ∀ X0 X3 X4 : G, (M.op (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) X4) = (M.op (M.op X3 X0) X4) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq5120 X0 x x X3 X4
       have i₂ := eq834 X0 (M.op x x) X4 X0
       grind)
    | exact superpose eq834 eq5120
    | exact resolve eq5120 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5120
  have eq5225 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op (M.op (M.op X5 X3) (M.op X1 X2)) X2)) (M.op (M.op X5 X3) (M.op X1 X2))) = (M.op (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq5084 X0 X1 X2 X3 X4 X5
       have i₂ := eq834 X2 X1 (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X2)) (M.op X5 X3)
       grind)
    | exact superpose eq834 eq5084
    | exact resolve eq5084 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5084
  have eq5247 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq194 eq5030
    | (have j0 := eq5030 X0 (σ x)
       grind)
    | exact resolve eq5030 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5030
  have eq5250 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq194 eq5016
    | (have j0 := eq5016 X0 (σ x)
       grind)
    | exact resolve eq5016 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq5016
  have eq5251 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq5013 X0 x
       have i₂ := eq187 X0 x
       grind)
    | (have i₁ := eq5013 X0 x
       have i₂ := eq187 X0 x
       grind)
    | exact superpose eq187 eq5013
    | (have j0 := eq5013 X0 x
       grind)
    | exact resolve eq5013 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq5013
  have eq5299 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq195 eq5202
    | exact resolve eq5202 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq5202
  have eq5303 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op X0 X1)) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq5207 X0 X1
       have i₂ := eq188 (M.op X0 X1) sF0
       grind)
    | exact superpose eq188 eq5207
    | exact resolve eq5207 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq5207
  have eq5305 : ∀ X0 X3 X4 : G, (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) X4) = (M.op (M.op X3 X0) X4) := by
    intro X0 X3 X4
    first
    | exact superpose eq3067 eq5212
    | exact resolve eq5212 eq3067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5212
  have eq5315 : ∀ X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op (M.op (M.op X5 X3) (M.op X1 X2)) X2)) (M.op (M.op X5 X3) (M.op X1 X2))) = (M.op (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (M.op (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (M.op X1 X2))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq5225 x X1 X2 X3 X4 X5
       have i₂ := eq834 X3 (M.op X1 X2) (M.op X1 X2) x
       grind)
    | exact superpose eq834 eq5225
    | exact resolve eq5225 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834 eq5225
  have eq5334 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq5201 eq5247
    | exact resolve eq5247 eq5201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5201 eq5247
  have eq5336 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq680 eq5250
    | exact resolve eq5250 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680 eq5250
  have eq5337 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq4867 eq5251
    | exact resolve eq5251 eq4867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5251
  have eq5373 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5299 X0 X1
       have i₂ := eq16 sF0 (M.op X0 X1) sF4
       grind)
    | exact superpose eq16 eq5299
    | exact resolve eq5299 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5299
  have eq5375 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5303 X0 X1
       have i₂ := eq16 sF0 (M.op X0 X1) sF0
       grind)
    | exact superpose eq16 eq5303
    | exact resolve eq5303 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5303
  have eq5379 : ∀ X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op (M.op (M.op X5 X3) (M.op X1 X2)) X2)) (M.op (M.op X5 X3) (M.op X1 X2))) = (M.op (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq5315 X2 x X3 X4 X5
       have i₂ := eq833 x (k (M.op sF4 sF4) sF4) X2
       grind)
    | exact superpose eq833 eq5315
    | exact resolve eq5315 eq833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833 eq5315
  have eq5393 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq5334 eq5336
    | exact resolve eq5336 eq5334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5334 eq5336
  have eq5412 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq5373 x x
       have i₂ := eq2947 sF0 x x
       grind)
    | exact superpose eq2947 eq5373
    | exact resolve eq5373 eq2947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5373
  have eq5414 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq5375 x x
       have i₂ := eq2947 sF0 x x
       grind)
    | exact superpose eq2947 eq5375
    | exact resolve eq5375 eq2947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5375
  have eq5418 : ∀ X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op (M.op (M.op X5 X3) (M.op X1 X2)) X2)) (M.op (M.op X5 X3) (M.op X1 X2))) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    intro X1 X2 X3 X4 X5
    first
    | exact superpose eq3067 eq5379
    | exact resolve eq5379 eq3067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3067 eq5379
  have eq5436 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq358 eq5412
    | exact resolve eq5412 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358 eq5412
  have eq5441 : ∀ X1 X2 X3 X4 X5 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (M.op X4 (M.op (M.op (M.op X5 X3) (M.op X1 X2)) X2)) (M.op (M.op X5 X3) (M.op X1 X2))) := by
    intro X1 X2 X3 X4 X5
    first
    | exact superpose eq5393 eq5418
    | exact resolve eq5418 eq5393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5418
  have eq5448 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5414 eq5436
    | exact resolve eq5436 eq5414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5414 eq5436
  have eq5453 : ∀ X1 X2 X3 X5 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) (M.op (M.op X5 X3) (M.op X1 X2))) := by
    intro X1 X2 X3 X5
    first
    | (have i₁ := eq5441 X1 X2 X3 x X5
       have i₂ := eq5305 (M.op (M.op (M.op X5 X3) (M.op X1 X2)) X2) x (M.op (M.op X5 X3) (M.op X1 X2))
       grind)
    | exact superpose eq5305 eq5441
    | exact resolve eq5441 eq5305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5441
  have eq5462 : ∀ X1 X2 X3 X5 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X5 X3) (M.op X1 X2))) := by
    intro X1 X2 X3 X5
    first
    | exact superpose eq5393 eq5453
    | exact resolve eq5453 eq5393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5393 eq5453
  have eq5469 : ∀ X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X1 X2))) := by
    intro X1 X2
    first
    | exact superpose eq723 eq5462
    | (have j0 := eq5462 X1 X2 (σ y) (σ x)
       grind)
    | exact resolve eq5462 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723 eq5462
  have eq5474 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X1)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    intro X1
    first
    | (have i₁ := eq5469 X1 x
       have i₂ := eq2947 sF4 X1 x
       grind)
    | exact superpose eq2947 eq5469
    | exact resolve eq5469 eq2947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2947 eq5469
  have eq5477 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X1)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    intro X1
    first
    | exact superpose eq5337 eq5474
    | exact resolve eq5474 eq5337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5337 eq5474
  have eq5480 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X1
    first
    | exact superpose eq5448 eq5477
    | exact resolve eq5477 eq5448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5448 eq5477
  have eq5495 : (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq4862 eq185
    | exact resolve eq185 eq4862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq4862
  have eq5843 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq5480 eq179
    | exact resolve eq179 eq5480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5848 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5480 eq181
    | exact resolve eq181 eq5480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq5480
  have eq5868 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq4867 eq5843
    | exact resolve eq5843 eq4867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5843
  have eq5895 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op x y)) X1) = (M.op (M.op X0 (M.op (σ x) (σ y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq5848 eq177
    | exact resolve eq177 eq5848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq5848
  have eq5902 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op X0 (M.op (σ x) (σ y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq4867 eq5895
    | exact resolve eq5895 eq4867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4867 eq5895
  have eq6125 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X0 (M.op (M.op x y) X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq5868 eq179
    | exact resolve eq179 eq5868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq5868
  have eq6164 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6125 x x
       have i₂ := eq5305 (M.op sF0 x) x x
       grind)
    | exact superpose eq5305 eq6125
    | exact resolve eq6125 eq5305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5305 eq6125
  have eq6193 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq5902 eq6164
    | exact resolve eq6164 eq5902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5902 eq6164
  have eq6530 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op X0 X1))) = (M.op (M.op x y) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6193 X0 (M.op X2 X1)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq6193
    | exact resolve eq6193 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6618 : ∀ X0 : G, (M.op (M.op x y) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq183 X0
       have i₂ := eq6193 X0 X0
       grind)
    | exact superpose eq6193 eq183
    | exact resolve eq183 eq6193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq6621 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op x y) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq6193 X1 X0
       grind)
    | exact superpose eq6193 eq16
    | exact resolve eq16 eq6193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6704 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X2 X1)) = (M.op (M.op x y) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6530 X0 X1 X2
       have i₂ := eq6621 (M.op X0 (M.op X0 X1)) X1 X2
       grind)
    | (have i₁ := eq6530 X0 y x
       have i₂ := eq6621 (M.op X0 (M.op X0 y)) X1 X2
       grind)
    | exact superpose eq6621 eq6530
    | exact resolve eq6530 eq6621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6530 eq6621
  have eq6724 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = (M.op (M.op x y) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6704 X0 X1 X2
       have i₂ := eq6193 X1 X0
       grind)
    | exact superpose eq6193 eq6704
    | exact resolve eq6704 eq6193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6704
  have eq6735 : ∀ X1 X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X2 X1)) := by
    intro X1 X2
    first
    | (have i₁ := eq6724 x X1 X2
       have i₂ := eq6193 x sF0
       grind)
    | exact superpose eq6193 eq6724
    | exact resolve eq6724 eq6193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6193 eq6724
  have eq10280 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4873 eq36
    | exact resolve eq36 eq4873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq4873
  have eq10288 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq10280
    | exact resolve eq10280 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10280
  have eq10291 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4876 eq10288
    | exact resolve eq10288 eq4876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10288
  have eq10418 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq10291 eq884
    | exact resolve eq884 eq10291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884 eq10291
  have eq10426 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10418
  have eq10487 : x = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10426 eq6735
    | exact resolve eq6735 eq10426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6735 eq10426
  have eq10488 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5495 eq10487
    | exact resolve eq10487 eq5495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10487
  have eq10508 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10488 eq27
    | exact resolve eq27 eq10488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10488
  have eq10542 : x = (M.op x y) := by
    first
    | (have r₁ := eq10508
       have r₂ := eq4876
       grind)
    | exact resolve eq10508 eq4876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10508
  have eq10549 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq10542
       grind)
    | exact superpose eq10542 eq22
    | exact resolve eq22 eq10542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq10562 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq5495
       have i₂ := eq10542
       grind)
    | exact superpose eq10542 eq5495
    | exact resolve eq5495 eq10542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5495 eq10542
  have eq10574 : (σ x) = (σ y) := by
    first
    | exact superpose eq10549 eq4863
    | exact resolve eq4863 eq10549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4863
  have eq10575 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq10549 eq20
    | exact resolve eq20 eq10549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10549
  have eq12646 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq10574 eq26
    | exact resolve eq26 eq10574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq12780 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq10562 eq6618
    | exact resolve eq6618 eq10562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6618 eq10562
  have eq12825 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq12780 eq38
    | exact resolve eq38 eq12780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq12780
  have eq12833 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq12825
    | exact resolve eq12825 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq12825
  have eq12837 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq4876 eq12833
    | exact resolve eq12833 eq4876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4876 eq12833
  have eq12841 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq10574 eq12837
    | exact resolve eq12837 eq10574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10574 eq12837
  have eq12848 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq12646
       have i₂ := eq28 sF2 sF2
       grind)
    | exact superpose eq28 eq12646
    | (have j1 := eq28 (σ x) (σ x)
       grind)
    | exact resolve eq12646 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq12890 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12841 eq12848
    | exact resolve eq12848 eq12841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12841 eq12848
  have eq12894 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12646 eq12890
    | exact resolve eq12890 eq12646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12646 eq12890
  have eq12895 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12894
  have eq12900 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq12895 eq27
    | exact resolve eq27 eq12895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq12895
  have eq12938 : False := by grind
  exact eq12938

/-- `Equation4419`: `x ◇ (x ◇ y) = (z ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation4419 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4419 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4419.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq619 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7429 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq619 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq619
    | (have j0 := eq619 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq619 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164286 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq7429 x y
       grind)
    | exact superpose eq7429 eq16
    | (have j1 := eq7429 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq7429 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq7429 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq7429 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq7429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7429
  have eq164553 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq164286
  have eq769509 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq164553
       grind)
    | exact superpose eq164553 eq16
    | exact resolve eq16 eq164553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq769511 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq164553
       grind)
    | exact superpose eq164553 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq164553
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq164553
       grind)
    | exact resolve eq13 eq164553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164553
  have eq769942 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq769511
  have eq769943 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq769942
  have eq770000 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq769943
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq769943
    | exact resolve eq769943 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769943
  have eq770009 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq14 eq770000
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq770000 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770000
  have eq770013 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq770009
       have r₂ := eq769509
       grind)
    | exact resolve eq770009 eq769509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769509 eq770009
  have eq770019 : y ≠ y ∨ x = y ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq770013
       grind)
    | exact superpose eq770013 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq770013
       grind)
    | exact resolve eq13 eq770013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq770399 : y ≠ y ∨ x = y ∨ y = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq770019
  have eq770400 : y = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq770399
  have eq770437 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq619 x y
       have i₂ := eq770400
       grind)
    | exact superpose eq770400 eq619
    | (have j0 := eq619 x y
       grind)
    | exact resolve eq619 eq770400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619 eq770400
  have eq770440 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq770437
  have eq774714 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq770440
       grind)
    | exact superpose eq770440 eq16
    | exact resolve eq16 eq770440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770440
  have eq775209 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq770013 eq774714
    | exact resolve eq774714 eq770013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770013 eq774714
  have eq775210 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq775209
  have eq775231 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq775210
       grind)
    | exact superpose eq775210 eq10
    | exact resolve eq10 eq775210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775210
  have eq775373 : x = y ∨ x = y := by
    first
    | (have i₁ := eq775231
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq775231
    | exact resolve eq775231 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775231
  have eq775374 : x = y := by grind
  clear eq775373
  have eq775377 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq775374
       grind)
    | exact superpose eq775374 eq16
    | exact resolve eq16 eq775374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775374
  have eq775378 : False := by grind
  exact eq775378
