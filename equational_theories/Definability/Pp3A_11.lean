import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pxx_pyx_pxy_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq70 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq70
    | exact resolve eq70 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq73 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq67 X0 x x X3 X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq67
    | exact resolve eq67 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq73 (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3) X0
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq73
    | exact resolve eq73 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 X0 x X0
       have i₂ := eq73 X0 X0 x
       grind)
    | exact superpose eq73 eq52
    | exact resolve eq52 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq178 X0 X1 X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq178
    | exact resolve eq178 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq196 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq212 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0 X0 X0
       have i₂ := eq185 X0
       grind)
    | exact superpose eq185 eq73
    | exact resolve eq73 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq213 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X0 X0 X1
       have i₂ := eq185 X0
       grind)
    | exact superpose eq185 eq52
    | exact resolve eq52 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq185
  have eq228 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op X0 X0) X1
       have i₂ := eq212 X0
       grind)
    | exact superpose eq212 eq9
    | exact resolve eq9 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq212 X0
       grind)
    | exact superpose eq212 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq212 X0
       grind)
    | exact resolve eq12 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq230 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq232 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq228 X0 X1
       have i₂ := eq72 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq228 X0 X1
       have i₂ := eq72 (M.op X0 X0) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq72 eq228
    | exact resolve eq228 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq316 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq196 x y
       grind)
    | exact superpose eq196 eq16
    | (have j1 := eq196 x y
       grind)
    | exact resolve eq16 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq196 X0 X0
       grind)
    | exact superpose eq196 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq196 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq196 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq196 X0 X1
       grind)
    | exact resolve eq12 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq342 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq323 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq345 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq342 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq342 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq342 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq506 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq232 X0 X1
       grind)
    | exact superpose eq232 eq9
    | exact resolve eq9 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq514 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq506 X0 X1
       have i₂ := eq212 X0
       grind)
    | exact superpose eq212 eq506
    | exact resolve eq506 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq525 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq232 X1 X0
       have i₂ := eq514 X1 X0
       grind)
    | exact superpose eq514 eq232
    | exact resolve eq232 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq528 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 X0
       have i₂ := eq514 X1 X0
       grind)
    | exact superpose eq514 eq9
    | exact resolve eq9 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq345 (M.op X0 X0) X1
       have i₂ := eq231 X0 (M.op X0 X0)
       grind)
    | exact superpose eq231 eq345
    | (have j0 := eq345 (M.op X0 X0) X1
       grind)
    | exact resolve eq345 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq763 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq741 X0 X1
       have i₂ := eq212 X0
       grind)
    | exact superpose eq212 eq741
    | (have j0 := eq741 X0 X1
       grind)
    | exact resolve eq741 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq741
  have eq764 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq763 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq819 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ (M.op X1 X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq514 X0 X2
       have i₂ := eq764 X1 X0
       grind)
    | exact superpose eq764 eq514
    | exact resolve eq514 eq764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq832 : ∀ X0 X1 : G, (k (τ X0) (M.op X1 X1)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 (M.op X1 X1)
       have i₂ := eq764 X1 X0
       grind)
    | exact superpose eq764 eq23
    | exact resolve eq23 eq764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq764
  have eq885 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 (M.op X1 X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq819 (σ X0) X1 X2
       have i₂ := eq15 X0 (M.op X1 X1)
       grind)
    | exact superpose eq15 eq819
    | exact resolve eq819 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819
  have eq1092 : ∀ X0 X2 : G, (M.op (σ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq885 X0 x X2
       have i₂ := eq231 x X0
       grind)
    | exact superpose eq231 eq885
    | exact resolve eq885 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885
  have eq1179 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq528 X0 (σ (M.op X1 X1))
       have i₂ := eq1092 X1 X0
       grind)
    | exact superpose eq1092 eq528
    | exact resolve eq528 eq1092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1612 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq832 X0 x
       have i₂ := eq231 x (τ X0)
       grind)
    | exact superpose eq231 eq832
    | exact resolve eq832 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231 eq832
  have eq2182 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1612 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1612
    | exact resolve eq1612 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1612
  have eq2758 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq2182 X0
       grind)
    | exact superpose eq2182 eq11
    | exact resolve eq11 eq2182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2182
  have eq3204 : (σ x) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq316
       have i₂ := eq2758 y
       grind)
    | exact superpose eq2758 eq316
    | exact resolve eq316 eq2758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq3205 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3204
       have i₂ := eq2758 y
       grind)
    | exact superpose eq2758 eq3204
    | exact resolve eq3204 eq2758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2758 eq3204
  have eq3206 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3205
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq3205
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq3205 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3205
  have eq3207 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by grind
  clear eq3206
  have eq35940 : (M.op y y) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq3207
       grind)
    | exact superpose eq3207 eq10
    | exact resolve eq10 eq3207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3207
  have eq36034 : y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq35940
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq35940
    | exact resolve eq35940 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35940
  have eq36035 : (σ x) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq36034
  have eq38044 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op X0 (M.op (M.op X0 X0) X1)) (M.op X0 X2)) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) X1) X0 (M.op X0 X2)
       have i₂ := eq195 X0 X0 X1 X2
       grind)
    | exact superpose eq195 eq9
    | exact resolve eq9 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq38108 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38044 X0 X1 X2
       have i₂ := eq514 X0 X1
       grind)
    | exact superpose eq514 eq38044
    | exact resolve eq38044 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38044
  have eq38438 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38108 (M.op (M.op X0 X0) (M.op X0 X1)) X2 X0
       have i₂ := eq213 X0 X1
       grind)
    | exact superpose eq213 eq38108
    | exact resolve eq38108 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq38108
  have eq38649 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38438 X0 X1 X2
       have i₂ := eq514 X0 (M.op X0 X1)
       grind)
    | exact superpose eq514 eq38438
    | exact resolve eq38438 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514 eq38438
  have eq770424 : (M.op y y) = (τ (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq36035
       grind)
    | exact superpose eq36035 eq10
    | exact resolve eq10 eq36035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36035
  have eq770872 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq770424
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq770424
    | exact resolve eq770424 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770424
  have eq770873 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq770872
  have eq771622 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq38649 y y X0
       have i₂ := eq770873
       grind)
    | exact superpose eq770873 eq38649
    | exact resolve eq38649 eq770873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38649 eq770873
  have eq771638 : ∀ X0 : G, x = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq771622 X0
       have i₂ := eq528 X0 y
       grind)
    | exact superpose eq528 eq771622
    | exact resolve eq771622 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771622
  have eq772008 : ∀ X0 X1 : G, (M.op (σ x) X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1092 y X0
       have i₂ := eq771638 X1
       grind)
    | exact superpose eq771638 eq1092
    | (have j1 := eq771638 X1
       grind)
    | exact resolve eq1092 eq771638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092
  have eq772290 : ∀ X0 : G, x = (M.op y x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq72 y y
       have i₂ := eq771638 X0
       grind)
    | exact superpose eq771638 eq72
    | (have j1 := eq771638 x
       grind)
    | exact resolve eq72 eq771638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq771638
  have eq777174 : x ≠ x ∨ x = (M.op y x) := by
    first
    | (have j0 := eq772290 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772290
  have eq777175 : x = (M.op y x) := by grind
  clear eq777174
  have eq777210 : y = (M.op x y) := by
    first
    | (have i₁ := eq528 x y
       have i₂ := eq777175
       grind)
    | exact superpose eq777175 eq528
    | exact resolve eq528 eq777175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528 eq777175
  have eq791068 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq772008 (σ y) X0
       grind)
    | exact superpose eq772008 eq16
    | (have j1 := eq772008 X0 X0
       grind)
    | exact resolve eq16 eq772008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772008
  have eq792276 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq791068 X0
       have i₂ := eq777210
       grind)
    | exact superpose eq777210 eq791068
    | (have j0 := eq791068 X0
       grind)
    | exact resolve eq791068 eq777210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777210 eq791068
  have eq792277 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq792276 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792276
  have eq792345 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq525 X0 y
       have i₂ := eq792277 y
       grind)
    | exact superpose eq792277 eq525
    | exact resolve eq525 eq792277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq792384 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1179 X0 y
       have i₂ := eq792277 y
       grind)
    | exact superpose eq792277 eq1179
    | exact resolve eq1179 eq792277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179 eq792277
  have eq809827 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq792384 (σ x)
       grind)
    | exact superpose eq792384 eq16
    | exact resolve eq16 eq792384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792384
  have eq810228 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq809827
       have i₂ := eq792345 x
       grind)
    | exact superpose eq792345 eq809827
    | exact resolve eq809827 eq792345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792345 eq809827
  have eq810229 : False := by grind
  exact eq810229

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_x_pxx_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  have eq60 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq23 eq37
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq70
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq70
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq87
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq87
    | exact resolve eq87 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq93
    | exact resolve eq93 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq109 : ∀ X0 : G, (M.op (M.op X0 (k (M.op X0 X0) X0)) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  have eq207 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq207 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq207
    | (have j0 := eq207 X0
       grind)
    | exact resolve eq207 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq210 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq61 eq14
    | exact resolve eq14 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq210
    | (have j0 := eq210 X0
       grind)
    | exact resolve eq210 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq343 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4)) X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3 X4
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq62
    | exact resolve eq62 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq62 X0 X1 X2 X3
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X1)) (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq60 eq62
    | exact resolve eq62 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq61 eq62
    | exact resolve eq62 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq62 x X0 X1 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq62
    | (have j0 := eq62 x X0 X1 y
       grind)
    | exact resolve eq62 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ x)) X1)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq62
    | (have j0 := eq62 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq62 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq360 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq62 X0 X1 X2 X3
       grind)
    | exact superpose eq62 eq14
    | exact resolve eq14 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq360 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq360
    | exact resolve eq360 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq363 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq352
    | (have j0 := eq352 X0 X1
       grind)
    | exact resolve eq352 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq364 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X1)) (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq351 X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq351
    | (have j0 := eq351 X0 X1
       grind)
    | exact resolve eq351 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq365 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq350 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq350
    | exact resolve eq350 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq423 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op (M.op (M.op X0 X0) (M.op (k (M.op X0 X0) X0) X1)) (k (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq62 (k (M.op X0 X0) X0) X0 X0 X1
       have i₂ := eq109 X0
       grind)
    | exact superpose eq109 eq62
    | (have j1 := eq109 X0
       grind)
    | exact resolve eq62 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq680 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq681 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq73 X0 X0
       grind)
    | exact superpose eq73 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq73 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq73 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq73 X0 X1
       grind)
    | exact resolve eq13 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq687 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq73 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq688 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq687 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq690 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq681 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq691 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq680 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq695 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq690 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq690 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq690 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq696 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq691 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq691
    | (have j0 := eq691 X0
       grind)
    | exact resolve eq691 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq3149 : (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq364 eq62
    | exact resolve eq62 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3159 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq3149 eq364
    | exact resolve eq364 eq3149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364 eq3149
  have eq3321 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | exact superpose eq61 eq365
    | exact resolve eq365 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3355 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq62 X0 X0 x X0
       have i₂ := eq365 X0 X0 x
       grind)
    | exact superpose eq365 eq62
    | exact resolve eq62 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq3372 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | exact superpose eq27 eq3321
    | (have j0 := eq3321 X0
       grind)
    | exact resolve eq3321 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3321
  have eq3388 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq365 X0 X0 X0
       have i₂ := eq3355 X0
       grind)
    | exact superpose eq3355 eq365
    | exact resolve eq365 eq3355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3355
  have eq3704 : ∀ X0 X1 X2 X3 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (M.op X0 (M.op (M.op X0 (σ x)) X1)) (σ x)) (M.op (M.op (σ x) (σ y)) X2)) (M.op (M.op (σ x) (σ y)) X3)) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq354 eq343
    | exact resolve eq343 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq3811 : ∀ X2 X3 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X2)) (M.op (M.op (σ x) (σ y)) X3)) (M.op (σ x) (σ y))) := by
    intro X2 X3
    first
    | (have i₁ := eq3704 x X2 X2 X3
       have i₂ := eq14 sF2 x X2
       grind)
    | exact superpose eq14 eq3704
    | exact resolve eq3704 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3704
  have eq4161 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) ≠ (M.op (M.op x y) (M.op x y)) ∨ (k X0 (M.op (M.op x y) (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq3159 eq13
    | (have j0 := eq13 X0 (M.op (M.op x y) (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op x y) (M.op x y))
       have r₂ := eq3159
       grind)
    | exact resolve eq13 eq3159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3159
  have eq4174 : ∀ X0 : G, (k X0 (M.op (M.op x y) (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq4161 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4161
  have eq4198 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op x y))) ≠ (σ (M.op (M.op x y) (M.op x y))) ∨ (k X0 (σ (M.op (M.op x y) (M.op x y)))) = X0 := by
    intro X0
    first
    | exact superpose eq4174 eq695
    | (have j0 := eq695 (M.op (M.op x y) (M.op x y)) X0
       grind)
    | exact resolve eq695 eq4174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695 eq4174
  have eq4210 : ∀ X0 : G, (k X0 (σ (M.op (M.op x y) (M.op x y)))) = X0 := by
    intro X0
    first
    | (have j0 := eq4198 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4198
  have eq5021 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  have eq5062 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq5021 X0
       have j1 := eq13 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq5021 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq5021 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5021
  have eq5335 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5062 (σ X0)
       have i₂ := eq73 X0 X0
       grind)
    | exact superpose eq73 eq5062
    | (have j1 := eq73 X0 X0
       grind)
    | exact resolve eq5062 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq5353 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq5335 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5335
  have eq5361 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq5353 X0
       have j1 := eq13 (σ (k X0 X0)) (σ X0)
       grind)
    | (have r₁ := eq5353 X0
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq5353 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5353
  have eq5365 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5361 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq5361
    | exact resolve eq5361 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5361
  have eq8198 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq423 X0 X1
       have i₂ := eq5062 X0
       grind)
    | exact superpose eq5062 eq423
    | (have j0 := eq423 X0 X1
       grind)
    | exact resolve eq423 eq5062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq8199 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8198 X0 X1
       have i₂ := eq362 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq8198 X0 X1
       have i₂ := eq362 (M.op X0 X0) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq362 eq8198
    | (have j0 := eq8198 X0 X1
       grind)
    | exact resolve eq8198 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8198
  have eq8322 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq8199 X0 X1
       grind)
    | exact superpose eq8199 eq14
    | (have j1 := eq8199 X0 X1
       grind)
    | exact resolve eq14 eq8199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8199
  have eq8348 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8322 X0 X1
       have i₂ := eq3388 X0
       grind)
    | exact superpose eq3388 eq8322
    | (have j0 := eq8322 X0 X1
       grind)
    | exact resolve eq8322 eq3388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3388 eq8322
  have eq8373 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 X0
       have i₂ := eq8348 X1 X0
       grind)
    | exact superpose eq8348 eq14
    | (have j1 := eq8348 X1 X1
       grind)
    | exact resolve eq14 eq8348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8348
  have eq10736 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq696 X0
       have j1 := eq688 X0
       grind)
    | (have r₁ := eq696 X0
       have r₂ := eq688 X0
       grind)
    | exact resolve eq696 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688 eq696
  have eq10737 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10736 X0
       have i₂ := eq5365 X0
       grind)
    | exact superpose eq5365 eq10736
    | (have j0 := eq10736 (k X0 X0)
       grind)
    | exact resolve eq10736 eq5365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5365 eq10736
  have eq10864 : ∀ X0 : G, (k X0 (σ (τ X0))) = (M.op (k X0 (σ (τ X0))) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq10737 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq10737
    | (have j0 := eq10737 (τ X0)
       grind)
    | exact resolve eq10737 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq10737
  have eq10952 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq10864 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10864
    | (have j0 := eq10864 X0
       grind)
    | exact resolve eq10864 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10864
  have eq10971 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10952 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10952
    | (have j0 := eq10952 X0
       grind)
    | exact resolve eq10952 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10952
  have eq14966 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq353 sF0 x
       have i₂ := eq8373 (M.op (M.op sF0 x) x) sF0
       grind)
    | exact superpose eq8373 eq353
    | (have j1 := eq8373 y x
       grind)
    | exact resolve eq353 eq8373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14968 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq354 sF4 x
       have i₂ := eq8373 (M.op (M.op sF4 sF2) x) sF4
       grind)
    | exact superpose eq8373 eq354
    | (have j1 := eq8373 (σ y) (σ x)
       grind)
    | exact resolve eq354 eq8373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8373
  have eq15072 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op x y)) ∨ x = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq14966 eq365
    | exact resolve eq365 eq14966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14966
  have eq15075 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ x = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq209 eq15072
    | exact resolve eq15072 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq15072
  have eq15152 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq14968 eq365
    | exact resolve eq365 eq14968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14968
  have eq15155 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq212 eq15152
    | exact resolve eq15152 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq15152
  have eq21176 : x = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq15075 eq353
    | exact resolve eq353 eq15075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353 eq15075
  have eq21223 : x = (M.op (M.op x y) x) := by grind
  clear eq21176
  have eq21231 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq21223 eq60
    | exact resolve eq60 eq21223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq21223
  have eq23918 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq15155 eq354
    | exact resolve eq354 eq15155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq15155
  have eq23965 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by grind
  clear eq23918
  have eq23972 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq23965 eq61
    | exact resolve eq61 eq23965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq23977 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq23965 eq363
    | exact resolve eq363 eq23965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq25367 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq3372 eq23977
    | exact resolve eq23977 eq3372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3372 eq23977
  have eq25417 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq25367 eq14
    | exact resolve eq14 eq25367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25367
  have eq25581 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) X0)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq23965 eq3811
    | exact resolve eq3811 eq23965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3811 eq23965
  have eq26004 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq25417 eq25581
    | exact resolve eq25581 eq25417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25417 eq25581
  have eq26067 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26004 eq14
    | exact resolve eq14 eq26004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26004
  have eq26175 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) X1) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) := by
    intro X0 X1
    first
    | exact superpose eq26067 eq365
    | exact resolve eq365 eq26067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq26208 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq26067 eq26175
    | exact resolve eq26175 eq26067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26067 eq26175
  have eq26446 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 X0
       have i₂ := eq26208 X0 X1
       grind)
    | exact superpose eq26208 eq14
    | exact resolve eq14 eq26208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26762 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26208 (M.op X1 X1) X0
       have i₂ := eq26446 X1 X0
       grind)
    | exact superpose eq26446 eq26208
    | exact resolve eq26208 eq26446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26208 eq26446
  have eq33586 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq94 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33587 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq33586
    | exact resolve eq33586 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33586
  have eq33598 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq33587
       have r₂ := eq28
       grind)
    | exact resolve eq33587 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33587
  have eq33630 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq33598 eq5062
    | exact resolve eq5062 eq33598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5062 eq33598
  have eq33679 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq33630
       have r₂ := eq13 x (σ x)
       grind)
    | (have r₁ := eq33630
       have r₂ := eq13 x x
       grind)
    | exact resolve eq33630 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33630
  have eq33690 : (τ (σ y)) = (k y x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq33679 eq92
    | exact resolve eq92 eq33679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq33691 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq33679 eq94
    | exact resolve eq94 eq33679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq33679
  have eq33702 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq33691
  have eq33710 : y = (k y x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq33690
    | exact resolve eq33690 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33690
  have eq33714 : y = (k y x) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq33710
       have r₂ := eq13 x x
       grind)
    | exact resolve eq33710 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33710
  have eq33716 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq70
       have i₂ := eq33714
       grind)
    | exact superpose eq33714 eq70
    | exact resolve eq70 eq33714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq33714
  have eq33743 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq33716
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq33716
    | exact resolve eq33716 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33716
  have eq33849 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq362 x x
       have i₂ := eq33702
       grind)
    | exact superpose eq33702 eq362
    | exact resolve eq362 eq33702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33702
  have eq33861 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq33849
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq33849
    | exact resolve eq33849 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33849
  have eq33945 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21231
       have i₂ := eq33861
       grind)
    | exact superpose eq33861 eq21231
    | exact resolve eq21231 eq33861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33861
  have eq34022 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq33945
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq33945
    | exact resolve eq33945 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq33945
  have eq34023 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq34022
  have eq34030 : y = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34023 eq30
    | exact resolve eq30 eq34023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq34023
  have eq34181 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq34030
    | exact resolve eq34030 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq34030
  have eq34182 : y = (M.op x y) := by grind
  clear eq34181
  have eq34189 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq34182 eq21
    | exact resolve eq21 eq34182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq34382 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq34189
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq34189
    | exact resolve eq34189 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34189
  have eq34392 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq34382 eq27
    | exact resolve eq27 eq34382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34483 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq34382 eq33743
    | exact resolve eq33743 eq34382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33743
  have eq37844 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq34483 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq11 eq34483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34483
  have eq37845 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq34392 eq37844
    | exact resolve eq37844 eq34392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37844
  have eq37856 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq37845
       have r₂ := eq28
       grind)
    | exact resolve eq37845 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37845
  have eq38003 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq4210 eq10971
    | (have j0 := eq10971 (σ (M.op (M.op x y) (M.op x y)))
       grind)
    | exact resolve eq10971 eq4210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4210 eq10971
  have eq38128 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by grind
  clear eq38003
  have eq38157 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
    first
    | exact superpose eq34182 eq38128
    | exact resolve eq38128 eq34182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34182 eq38128
  have eq80769 : ∀ X0 : G, (σ (M.op y y)) = (M.op X0 (σ (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq26762 X0 (σ (M.op y y))
       have i₂ := eq38157
       grind)
    | exact superpose eq38157 eq26762
    | exact resolve eq26762 eq38157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26762 eq38157
  have eq115957 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq37856 eq23972
    | exact resolve eq23972 eq37856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23972 eq37856
  have eq116077 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq115957
    | exact resolve eq115957 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq115957
  have eq116080 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq34382 eq116077
    | exact resolve eq116077 eq34382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116077
  have eq116082 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq116080
       have r₂ := eq28
       grind)
    | exact resolve eq116080 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116080
  have eq116172 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq116082 eq362
    | exact resolve eq362 eq116082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362 eq116082
  have eq116192 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq34392 eq116172
    | exact resolve eq116172 eq34392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116172
  have eq116209 : y = (M.op x x) := by
    first
    | (have r₁ := eq116192
       have r₂ := eq28
       grind)
    | exact resolve eq116192 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116192
  have eq116222 : y = (M.op y y) := by
    first
    | (have i₁ := eq21231
       have i₂ := eq116209
       grind)
    | exact superpose eq116209 eq21231
    | exact resolve eq21231 eq116209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21231 eq116209
  have eq116427 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq80769 X0
       have i₂ := eq116222
       grind)
    | exact superpose eq116222 eq80769
    | exact resolve eq80769 eq116222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80769 eq116222
  have eq116570 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq116427 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq116427
    | (have j0 := eq116427 X0
       grind)
    | exact resolve eq116427 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq116427
  have eq116595 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq34382 eq116570
    | exact resolve eq116570 eq34382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34382 eq116570
  have eq122157 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq116595 eq34392
    | exact resolve eq34392 eq116595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34392 eq116595
  have eq122237 : False := by grind
  exact eq122237

/-- `Equation2653`: `x = ((x ◇ x) ◇ (y ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_y_pxy_Equation2653 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2653 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2653.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X1) = X0 := by
    intro X0 X1
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
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq14 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq73
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq73
    | exact resolve eq73 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq80 : (M.op x x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq79
    | exact resolve eq79 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq475 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op X0 X0)
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq481 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X1
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3506 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq481 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq481
    | exact resolve eq481 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq3507 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq3506 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq3506
    | exact resolve eq3506 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3506
  have eq3510 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3507 X0
       have i₂ := eq53 (M.op X0 X0)
       grind)
    | exact superpose eq53 eq3507
    | exact resolve eq3507 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3507
  have eq3511 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3510 X0
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq3510
    | exact resolve eq3510 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq3510
  have eq3734 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq475 X0
       have i₂ := eq3511 X0
       grind)
    | exact superpose eq3511 eq475
    | exact resolve eq475 eq3511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475 eq3511
  have eq3742 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq3734 X0
       grind)
    | exact superpose eq3734 eq14
    | exact resolve eq14 eq3734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3734
  have eq17308 : ∀ X0 : G, y = (M.op (M.op (M.op x x) X0) (M.op (M.op X0 X0) X0)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq3742 X0 y
       have i₂ := eq80
       grind)
    | exact superpose eq80 eq3742
    | exact resolve eq3742 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq17329 : x = y ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq17308 x
       have i₂ := eq3742 x x
       grind)
    | exact superpose eq3742 eq17308
    | exact resolve eq17308 eq3742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17308
  have eq17330 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by grind
  clear eq17329
  have eq17376 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq17330 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq17330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17330
  have eq17377 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq17376
    | exact resolve eq17376 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17376
  have eq17388 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq17377
       have r₂ := eq28
       grind)
    | exact resolve eq17377 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17377
  have eq17434 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ x)) X0) (M.op (M.op X0 X0) X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq17388 eq3742
    | exact resolve eq3742 eq17388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17388
  have eq17455 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq17434 x
       have i₂ := eq3742 x sF2
       grind)
    | exact superpose eq3742 eq17434
    | exact resolve eq17434 eq3742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3742 eq17434
  have eq17456 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq17455
  have eq17490 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq17456 eq30
    | exact resolve eq30 eq17456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq17456
  have eq17618 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq17490
    | exact resolve eq17490 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq17490
  have eq17619 : x = y := by grind
  clear eq17618
  have eq17879 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq17619
       grind)
    | exact superpose eq17619 eq19
    | exact resolve eq19 eq17619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq17880 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq17619
       grind)
    | exact superpose eq17619 eq25
    | exact resolve eq25 eq17619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq17619
  have eq18004 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq17880
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17880
    | exact resolve eq17880 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq17880
  have eq18023 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18004 eq27
    | exact resolve eq27 eq18004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq18004
  have eq18877 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq18023 eq65
    | exact resolve eq65 eq18023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq18023
  have eq18950 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq18877
       have i₂ := eq17879
       grind)
    | exact superpose eq17879 eq18877
    | exact resolve eq18877 eq17879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17879 eq18877
  have eq18964 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18950 eq15
    | exact resolve eq15 eq18950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18950
  have eq19051 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq18964
    | exact resolve eq18964 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq18964
  have eq19072 : False := by grind
  exact eq19072

/-- `Equation2653`: `x = ((x ◇ x) ◇ (y ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxy_pxx_pxy_Equation2653 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2653 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2653.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X1) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq18
  have eq29 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq29
  have eq42 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq9 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (σ (M.op X0 X0))) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq122 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq42 (M.op X0 X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq42
    | exact resolve eq42 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq9
    | exact resolve eq9 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X0)) (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq9
    | exact resolve eq9 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq9
    | exact resolve eq9 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
  have eq523 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq127 (M.op (M.op X0 X0) X0) X0
       have i₂ := eq126 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq126 eq127
    | exact resolve eq127 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq525 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq127 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq127
    | exact resolve eq127 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq527 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq525 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq525
    | exact resolve eq525 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq528 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq523 X0
       have i₂ := eq125 X0
       grind)
    | exact superpose eq125 eq523
    | exact resolve eq523 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq531 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq527 X0
       have i₂ := eq42 (M.op X0 X0)
       grind)
    | exact superpose eq42 eq527
    | exact resolve eq527 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq532 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq531 X0
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq531
    | exact resolve eq531 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq533 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq532 (M.op X0 X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq532
    | exact resolve eq532 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq540 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq533 X0
       have i₂ := eq532 X0
       grind)
    | exact superpose eq532 eq533
    | exact resolve eq533 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq606 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq528 X0
       grind)
    | exact superpose eq528 eq9
    | exact resolve eq9 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq607 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq528 X0
       grind)
    | exact superpose eq528 eq9
    | exact resolve eq9 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq650 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) X1) = (M.op (M.op X0 (M.op X2 X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq606 X0 X2
       have i₂ := eq606 X0 X1
       grind)
    | exact superpose eq606 eq606
    | exact resolve eq606 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X1) = (M.op (M.op X1 X0) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq606 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq528 X0
       grind)
    | exact superpose eq528 eq606
    | exact resolve eq606 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq660 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq125 X0
       have i₂ := eq606 X0 X1
       grind)
    | exact superpose eq606 eq125
    | exact resolve eq125 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op X1 X1)) X1) (M.op X2 X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq127 X0 X2
       have i₂ := eq606 X0 X1
       grind)
    | exact superpose eq606 eq127
    | exact resolve eq127 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq667 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 (M.op X1 X1)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq540 X0
       have i₂ := eq606 X0 X1
       grind)
    | exact superpose eq606 eq540
    | exact resolve eq540 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq760 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (σ (M.op X0 X0))) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq660 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq660
    | exact resolve eq660 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq761 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (τ (M.op X0 X0))) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq660 X1 (τ X0)
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq660
    | exact resolve eq660 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq775 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq660 (M.op X0 X0) x
       have i₂ := eq9 X0 x
       grind)
    | exact superpose eq9 eq660
    | exact resolve eq660 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq777 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq660 (σ (M.op X0 X0)) x
       have i₂ := eq47 X0 x
       grind)
    | exact superpose eq47 eq660
    | exact resolve eq660 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq660
  have eq1163 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq667 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq607 X0 X0
       grind)
    | exact superpose eq607 eq667
    | exact resolve eq667 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607 eq667
  have eq1692 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq168
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq168
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq168
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq168
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq168 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq1693 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1692
  have eq5278 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op (M.op X1 X1) X1) (M.op (M.op X1 X1) X1)) (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq652 (M.op (M.op X1 X1) X1) (M.op X0 X1)
       have i₂ := eq652 X1 X0
       grind)
    | exact superpose eq652 eq652
    | exact resolve eq652 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq5443 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op (M.op X1 X1) X1) (M.op X1 X1)) (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5278 X0 X1
       have i₂ := eq122 X1
       grind)
    | exact superpose eq122 eq5278
    | exact resolve eq5278 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq5278
  have eq5498 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op (M.op X0 X0) X0) (M.op X1 (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5443 X0 X1
       have i₂ := eq532 X1
       grind)
    | exact superpose eq532 eq5443
    | exact resolve eq5443 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5443
  have eq5538 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X1 X1)) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5498 X0 X1
       have i₂ := eq540 X1
       grind)
    | exact superpose eq540 eq5498
    | exact resolve eq5498 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5498
  have eq7406 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1))) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X0 (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1163 X1 (M.op (M.op X0 X0) (M.op X1 X1))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq1163
    | exact resolve eq1163 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq20073 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1693
       grind)
    | exact superpose eq1693 eq16
    | exact resolve eq16 eq1693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1693
  have eq20074 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq20073
       have r₂ := eq22 x
       grind)
    | exact resolve eq20073 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20073
  have eq31307 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 X1)))) (M.op X2 X2)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq662 X0 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       have i₂ := eq650 (M.op X0 (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 X1)))) (M.op X1 X1) X2
       grind)
    | (have i₁ := eq662 X0 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       have i₂ := eq650 (M.op X0 (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 X1)))) X2 (M.op X1 X1)
       grind)
    | exact superpose eq650 eq662
    | exact resolve eq662 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650 eq662
  have eq31778 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op X1 (M.op (M.op X1 X1) X1)))) (M.op X2 X2)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31307 X0 X1 X2
       have i₂ := eq7406 X1 X1
       grind)
    | exact superpose eq7406 eq31307
    | exact resolve eq31307 eq7406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7406 eq31307
  have eq31934 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op X1 X1))) (M.op X2 X2)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31778 X0 X1 X2
       have i₂ := eq540 X1
       grind)
    | exact superpose eq540 eq31778
    | exact resolve eq31778 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540 eq31778
  have eq31988 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X1 X1) X1) (M.op X1 X1))) (M.op X2 X2)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31934 X0 X1 X2
       have i₂ := eq5538 X1 X1
       grind)
    | exact superpose eq5538 eq31934
    | exact resolve eq31934 eq5538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5538 eq31934
  have eq32016 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31988 X0 X1 X2
       have i₂ := eq532 X1
       grind)
    | exact superpose eq532 eq31988
    | exact resolve eq31988 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532 eq31988
  have eq33231 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op (M.op (M.op X1 X2) (τ (M.op X0 X0))) (τ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32016 X1 X2 (τ X0)
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq32016
    | exact resolve eq32016 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33259 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (σ (M.op X1 X1))) (M.op (M.op X0 X0) (σ (M.op X1 X1)))) = (M.op (M.op (M.op X0 X0) X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32016 (M.op (M.op X0 X0) (σ (M.op X1 X1))) (σ X1) X0
       have i₂ := eq760 X1 (M.op X0 X0)
       grind)
    | exact superpose eq760 eq32016
    | exact resolve eq32016 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760
  have eq33580 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op (M.op (M.op (M.op (σ X0) X1) (M.op X2 X2)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X0
       have i₂ := eq32016 (σ X0) X1 X2
       grind)
    | exact superpose eq32016 eq22
    | exact resolve eq22 eq32016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32016
  have eq148334 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (τ (M.op (M.op (M.op (M.op (σ X0) X1) (M.op X2 X2)) X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq33580 X0 X1 X2
       grind)
    | exact superpose eq33580 eq10
    | exact resolve eq10 eq33580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33580
  have eq236266 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) = (τ (M.op (M.op (M.op (M.op (σ (τ X0)) X1) (M.op X2 X2)) X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X0
       have i₂ := eq148334 (τ X0) X1 X2
       grind)
    | exact superpose eq148334 eq67
    | exact resolve eq67 eq148334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq236742 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) = (τ (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq236266 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq236266
    | exact resolve eq236266 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236266
  have eq269665 : ∀ X0 X1 X2 : G, (τ (M.op (M.op (M.op X0 (M.op X2 X2)) X2) (σ X1))) = (τ (M.op (M.op (M.op X0 X0) (σ (M.op X1 X1))) (M.op (M.op X0 X0) (σ (M.op X1 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq236742 (M.op (M.op X0 X0) (σ (M.op X1 X1))) (σ X1) X2
       have i₂ := eq46 X1 X0
       grind)
    | exact superpose eq46 eq236742
    | exact resolve eq236742 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq236742
  have eq271313 : ∀ X0 X1 X2 : G, (τ (M.op (M.op (M.op X0 X0) X0) (σ X1))) = (τ (M.op (M.op (M.op X0 (M.op X2 X2)) X2) (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq269665 X0 X1 X2
       have i₂ := eq33259 X0 X1
       grind)
    | exact superpose eq33259 eq269665
    | exact resolve eq269665 eq33259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33259 eq269665
  have eq275828 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op y (τ (M.op X0 X0))) (τ X0)) y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq33231 X0 x y
       have i₂ := eq20074
       grind)
    | exact superpose eq20074 eq33231
    | exact resolve eq33231 eq20074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20074 eq33231
  have eq275842 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq275828 x
       have i₂ := eq761 x y
       grind)
    | exact superpose eq761 eq275828
    | exact resolve eq275828 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761 eq275828
  have eq452141 : ∀ X0 : G, (M.op x x) = (τ (M.op (M.op (M.op (σ y) (M.op X0 X0)) X0) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq148334 x (σ y) X0
       have i₂ := eq275842
       grind)
    | exact superpose eq275842 eq148334
    | exact resolve eq148334 eq275842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148334 eq275842
  have eq452249 : (M.op x x) = (τ (M.op (M.op (M.op (σ y) (σ y)) (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq452141 x
       have i₂ := eq271313 (σ y) y x
       grind)
    | exact superpose eq271313 eq452141
    | exact resolve eq452141 eq271313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271313 eq452141
  have eq452310 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq452249
       have i₂ := eq125 (σ y)
       grind)
    | exact superpose eq125 eq452249
    | exact resolve eq452249 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq452249
  have eq452348 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq452310
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq452310
    | exact resolve eq452310 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452310
  have eq452349 : (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq452348
  have eq452373 : y = (τ (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq452349
       grind)
    | exact superpose eq452349 eq10
    | exact resolve eq10 eq452349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452349
  have eq452855 : x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq452373
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq452373
    | exact resolve eq452373 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452373
  have eq453595 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq452855
       grind)
    | exact superpose eq452855 eq16
    | exact resolve eq16 eq452855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452855
  have eq453596 : y = (M.op x x) := by
    first
    | (have r₁ := eq453595
       have r₂ := eq22 x
       grind)
    | exact resolve eq453595 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq453595
  have eq453718 : y = (M.op x y) := by
    first
    | (have i₁ := eq775 x
       have i₂ := eq453596
       grind)
    | exact superpose eq453596 eq775
    | exact resolve eq775 eq453596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq453719 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq777 x
       have i₂ := eq453596
       grind)
    | exact superpose eq453596 eq777
    | exact resolve eq777 eq453596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777 eq453596
  have eq461723 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq453719
       grind)
    | exact superpose eq453719 eq16
    | exact resolve eq16 eq453719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453719
  have eq461853 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq461723
       have i₂ := eq453718
       grind)
    | exact superpose eq453718 eq461723
    | exact resolve eq461723 eq453718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453718 eq461723
  have eq461854 : False := by grind
  exact eq461854

/-- `Equation2656`: `x = ((x ◇ x) ◇ (y ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_y_pyy_pxy_Equation2656 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2656 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2656.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) = X0 := by
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
  have eq29 : x = (τ (σ x)) := by
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
  have eq31 : y = (τ (σ y)) := by
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
  have eq39 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq44 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq44 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq44
    | exact resolve eq44 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq141 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq59 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq174 : y ≠ (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op x y)) x) = X0 := by
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
  have eq177 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op (M.op X0 X1) (M.op X0 X1)) X0 X1
       have i₂ := eq16 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq176 (M.op sF0 sF0)
       have i₂ := eq16 sF0 sF0 sF0
       grind)
    | exact superpose eq16 eq176
    | exact resolve eq176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X0 X0) (M.op x y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq176 eq179
    | exact resolve eq179 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq578 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 X0
       have i₂ := eq179 X0 X0
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq177 (M.op X0 X1)
       have i₂ := eq179 X0 X1
       grind)
    | exact superpose eq179 eq177
    | exact resolve eq177 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq584 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq176 (M.op X0 X1)
       have i₂ := eq179 X0 X1
       grind)
    | exact superpose eq179 eq176
    | exact resolve eq176 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq611 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq567 eq16
    | exact resolve eq16 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq614 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq611 X0
       have i₂ := eq179 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq179 eq611
    | exact resolve eq611 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq616 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq614 X0
       have i₂ := eq179 X0 X0
       grind)
    | exact superpose eq179 eq614
    | exact resolve eq614 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq641 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq643 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq689 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq821 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq641
       grind)
    | exact superpose eq641 eq40
    | exact resolve eq40 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq822 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq821
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq821
    | exact resolve eq821 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq824 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq822
    | exact resolve eq822 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq1616 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq583 (M.op X0 X0) X0
       have i₂ := eq616 X0
       grind)
    | exact superpose eq616 eq583
    | exact resolve eq583 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1749 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq578 X0
       have i₂ := eq1616 X0
       grind)
    | exact superpose eq1616 eq578
    | exact resolve eq578 eq1616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq1770 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq1616 eq583
    | exact resolve eq583 eq1616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616
  have eq1782 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq583 eq1770
    | exact resolve eq1770 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583 eq1770
  have eq1818 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq177 eq1749
    | exact resolve eq1749 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq1749
  have eq1851 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 (M.op X0 X0) X0
       have i₂ := eq1818 X0
       grind)
    | exact superpose eq1818 eq13
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq1818 X0
       grind)
    | exact resolve eq13 eq1818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1818
  have eq1872 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1851 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1851
  have eq1905 : (τ (σ x)) = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | (have i₁ := eq141 (M.op sF2 sF2)
       have i₂ := eq1872 sF2
       grind)
    | exact superpose eq1872 eq141
    | exact resolve eq141 eq1872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq1910 : x = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | exact superpose eq29 eq1905
    | exact resolve eq1905 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1905
  have eq2646 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq584 (M.op X0 X0) X0
       have i₂ := eq616 X0
       grind)
    | exact superpose eq616 eq584
    | exact resolve eq584 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq2757 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) x) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq616 X0
       have i₂ := eq2646 X0
       grind)
    | exact superpose eq2646 eq616
    | exact resolve eq616 eq2646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq2778 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) x) (M.op X0 X0)) = (M.op (M.op (M.op X0 (M.op x y)) x) (M.op (M.op X0 (M.op x y)) x)) := by
    intro X0
    first
    | (have i₁ := eq179 (M.op X0 X0) X0
       have i₂ := eq2646 X0
       grind)
    | exact superpose eq2646 eq179
    | exact resolve eq179 eq2646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2646
  have eq2811 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) x) (M.op X0 X0)) = (M.op (M.op (M.op X0 (M.op x y)) x) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq2778 X0
       have i₂ := eq179 (M.op X0 sF0) x
       grind)
    | exact superpose eq179 eq2778
    | exact resolve eq2778 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2778
  have eq2821 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) x) (M.op X0 (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq2757 eq2811
    | exact resolve eq2811 eq2757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2757 eq2811
  have eq3193 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq824 eq643
    | exact resolve eq643 eq824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq3203 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq3193
       have r₂ := eq27
       grind)
    | exact resolve eq3193 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3193
  have eq3209 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq3203 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq3203
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq3203
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3203
       grind)
    | exact resolve eq13 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3203
  have eq3217 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq3209
  have eq3235 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq3217 eq90
    | exact resolve eq90 eq3217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq3217
  have eq3246 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq31 eq3235
    | exact resolve eq3235 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3235
  have eq3249 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq3246
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq3246
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq3246
       have r₂ := eq13 x y
       grind)
    | exact resolve eq3246 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3246
  have eq3253 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq641
       have i₂ := eq3249
       grind)
    | exact superpose eq3249 eq641
    | exact resolve eq641 eq3249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq3254 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq3249
       grind)
    | exact superpose eq3249 eq35
    | exact resolve eq35 eq3249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq3249
  have eq3260 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3253
  have eq3266 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3254
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3254
    | exact resolve eq3254 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3254
  have eq3270 : x ≠ x ∨ y = (M.op x y) ∨ (k y x) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq3260
       grind)
    | exact superpose eq3260 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq3260
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq3260
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq3260
       grind)
    | exact resolve eq12 eq3260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3274 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq179 y x
       have i₂ := eq3260
       grind)
    | exact superpose eq3260 eq179
    | exact resolve eq179 eq3260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3260
  have eq3280 : y = (M.op x y) ∨ (k y x) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3270
  have eq3283 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3274
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3274
    | exact resolve eq3274 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3274
  have eq3284 : y = (M.op x y) ∨ (k y x) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3280
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3280
    | exact resolve eq3280 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3280
  have eq3285 : y = (M.op x y) ∨ (k y x) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3284
  have eq3289 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3283 eq3285
    | exact resolve eq3285 eq3283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3283 eq3285
  have eq3296 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3266 eq643
    | exact resolve eq643 eq3266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643 eq3266
  have eq3304 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3296
  have eq3374 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq3289
       grind)
    | exact superpose eq3289 eq39
    | exact resolve eq39 eq3289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq3289
  have eq3377 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3374
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3374
    | exact resolve eq3374 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3374
  have eq3379 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq3377
    | exact resolve eq3377 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3377
  have eq3543 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3304 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq3304
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq3304
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq3304
       grind)
    | exact resolve eq12 eq3304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3547 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3304 eq179
    | exact resolve eq179 eq3304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3304
  have eq3554 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3543
  have eq3558 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq3547
    | exact resolve eq3547 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3547
  have eq3559 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq3554
    | exact resolve eq3554 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3554
  have eq3560 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq3559
  have eq3563 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3379 eq3560
    | exact resolve eq3560 eq3379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3379 eq3560
  have eq3678 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3563 eq3558
    | exact resolve eq3558 eq3563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3558 eq3563
  have eq3716 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3678
  have eq3725 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq3716
       have r₂ := eq27
       grind)
    | exact resolve eq3716 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3716
  have eq3731 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3725 eq175
    | (have r₁ := eq175
       have r₂ := eq3725
       grind)
    | exact resolve eq175 eq3725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq3778 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq3731
  have eq3799 : (τ (σ x)) = (k y (τ (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3778 eq107
    | exact resolve eq107 eq3778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq3778
  have eq3810 : x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq3799
    | exact resolve eq3799 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3799
  have eq3813 : x = (k y x) := by
    first
    | (have r₁ := eq3810
       have r₂ := eq174
       grind)
    | exact resolve eq3810 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq3810
  have eq3818 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq3813
       grind)
    | exact superpose eq3813 eq36
    | exact resolve eq36 eq3813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq3821 : x ≠ x ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq689 y x
       have i₂ := eq3813
       grind)
    | exact superpose eq3813 eq689
    | (have j0 := eq689 y x
       grind)
    | (have r₁ := eq689 y x
       have r₂ := eq3813
       grind)
    | exact resolve eq689 eq3813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3822 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq3821
  have eq3824 : x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3822
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3822
    | exact resolve eq3822 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3822
  have eq3827 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq3818
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3818
    | exact resolve eq3818 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3818
  have eq3835 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3827 eq689
    | (have j0 := eq689 (σ y) (σ x)
       grind)
    | (have r₁ := eq689 (σ y) (σ x)
       have r₂ := eq3827
       grind)
    | exact resolve eq689 eq3827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3836 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3835
  have eq3838 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3836
    | exact resolve eq3836 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3836
  have eq3909 : x ≠ x ∨ y = (M.op x y) ∨ (k y x) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq3824
       grind)
    | exact superpose eq3824 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq3824
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq3824
       grind)
    | exact resolve eq12 eq3824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3913 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq179 y x
       have i₂ := eq3824
       grind)
    | exact superpose eq3824 eq179
    | exact resolve eq179 eq3824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3824
  have eq3920 : y = (M.op x y) ∨ (k y x) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq3909
  have eq3924 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3913
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3913
    | exact resolve eq3913 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3913
  have eq3925 : y = (M.op x y) ∨ (k y x) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3920
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3920
    | exact resolve eq3920 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3920
  have eq3926 : y = (M.op x y) ∨ (k y x) = (M.op x x) := by grind
  clear eq3925
  have eq3929 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3926
       have i₂ := eq3813
       grind)
    | exact superpose eq3813 eq3926
    | exact resolve eq3926 eq3813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3813 eq3926
  have eq3931 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3924 eq3929
    | exact resolve eq3929 eq3924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3929
  have eq3933 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq3931
       grind)
    | exact superpose eq3931 eq24
    | exact resolve eq24 eq3931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3949 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq3933
    | exact resolve eq3933 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3933
  have eq3992 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3838 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq3838
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq3838
       grind)
    | exact resolve eq12 eq3838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3996 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3838 eq179
    | exact resolve eq179 eq3838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq3838
  have eq4003 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3992
  have eq4007 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3996
    | exact resolve eq3996 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3996
  have eq4008 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq4003
    | exact resolve eq4003 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4003
  have eq4009 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
  clear eq4008
  have eq4012 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3827 eq4009
    | exact resolve eq4009 eq3827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3827 eq4009
  have eq4055 : x = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1872 x
       have i₂ := eq3924
       grind)
    | exact superpose eq3924 eq1872
    | exact resolve eq1872 eq3924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1872 eq3924
  have eq4078 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3931 eq4055
    | exact resolve eq4055 eq3931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4055
  have eq4260 : x = (k (τ (σ x)) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4012 eq1910
    | exact resolve eq1910 eq4012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1910
  have eq4264 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4012 eq4007
    | exact resolve eq4007 eq4012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4007 eq4012
  have eq4297 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4264
  have eq4311 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq4260
    | exact resolve eq4260 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4260
  have eq4319 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4297 eq27
    | exact resolve eq27 eq4297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4359 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4297 eq1782
    | exact resolve eq1782 eq4297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1782
  have eq4366 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq4370 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq4359
    | exact resolve eq4359 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4359
  have eq4384 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4297 eq4370
    | exact resolve eq4370 eq4297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4297 eq4370
  have eq4387 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3949 eq4319
    | (have r₁ := eq4319
       have r₂ := eq3949
       grind)
    | exact resolve eq4319 eq3949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4388 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4387
  have eq4391 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4388 eq27
    | exact resolve eq27 eq4388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4851 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3949 eq4391
    | exact resolve eq4391 eq3949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3949 eq4391
  have eq4852 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq4851
  have eq5219 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq689 x x
       have i₂ := eq4311
       grind)
    | exact superpose eq4311 eq689
    | (have j0 := eq689 x x
       grind)
    | (have r₁ := eq689 x x
       have r₂ := eq4311
       grind)
    | exact resolve eq689 eq4311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689 eq4311
  have eq5220 : x ≠ x ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5219
  have eq5221 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5220
  have eq5294 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4384 eq11
    | exact resolve eq11 eq4384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4384
  have eq5307 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5294
  have eq5315 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq5307
       have r₂ := eq4366
       grind)
    | exact resolve eq5307 eq4366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4366 eq5307
  have eq5458 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5315 eq97
    | exact resolve eq97 eq5315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq5315
  have eq5471 : y = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq5458
    | exact resolve eq5458 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5458
  have eq5475 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4388 eq5471
    | exact resolve eq5471 eq4388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4388 eq5471
  have eq5498 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5475 eq4078
    | exact resolve eq4078 eq5475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4078 eq5475
  have eq5510 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq5498
  have eq5569 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5510 eq3725
    | exact resolve eq3725 eq5510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3725 eq5510
  have eq5571 : (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq5569
  have eq5587 : y = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5571 eq31
    | exact resolve eq31 eq5571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq5571
  have eq5637 : x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq5587
    | exact resolve eq5587 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq5587
  have eq5649 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3931 eq5637
    | exact resolve eq5637 eq3931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3931 eq5637
  have eq5650 : y = (M.op x y) := by grind
  clear eq5649
  have eq5656 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq5650
       grind)
    | exact superpose eq5650 eq18
    | exact resolve eq18 eq5650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq5657 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq5650
       grind)
    | exact superpose eq5650 eq24
    | exact resolve eq24 eq5650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq5650
  have eq5672 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5657 eq20
    | exact resolve eq20 eq5657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq5715 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5672 eq4319
    | (have r₁ := eq4319
       have r₂ := eq5672
       grind)
    | exact resolve eq4319 eq5672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4319
  have eq5721 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5715
  have eq5740 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq5721 eq27
    | exact resolve eq27 eq5721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq5793 : (σ x) ≠ (σ y) := by
    first
    | exact superpose eq5672 eq5740
    | exact resolve eq5740 eq5672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5672 eq5740
  have eq5811 : x = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    first
    | exact superpose eq5656 eq2821
    | exact resolve eq2821 eq5656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2821 eq5656
  have eq5829 : x = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq181 eq5811
    | exact resolve eq5811 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq5811
  have eq6118 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq5829 eq182
    | exact resolve eq182 eq5829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq5829
  have eq6168 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5221
       have i₂ := eq6118
       grind)
    | exact superpose eq6118 eq5221
    | exact resolve eq5221 eq6118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5221 eq6118
  have eq6226 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5721 eq6168
    | exact resolve eq6168 eq5721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5721 eq6168
  have eq6237 : x = (M.op x y) := by
    first
    | (have r₁ := eq6226
       have r₂ := eq4852
       grind)
    | exact resolve eq6226 eq4852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4852 eq6226
  have eq6242 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq6237
       grind)
    | exact superpose eq6237 eq22
    | exact resolve eq22 eq6237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6237
  have eq6296 : (σ x) = (σ y) := by
    first
    | exact superpose eq6242 eq5657
    | exact resolve eq5657 eq6242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5657 eq6242
  have eq6316 : False := by grind
  exact eq6316

/-- `Equation2663`: `x = ((x ◇ y) ◇ (x ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(Y,Y) else if m(X,X) = m(X,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxx_pxy_pyy_x_pxy_Equation2663 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2663 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2663.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
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
  have eq28 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq43 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35
    | (have j0 := eq35 x
       grind)
    | exact resolve eq35 eq22
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
  have eq49 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X1 (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 (M.op (M.op X0 X1) (M.op X0 X1))
       grind)
    | (have r₁ := eq13 X1 (M.op (M.op (M.op X1 X1) X1) (M.op (M.op X1 X1) X1))
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq62 (σ X0)
       grind)
    | exact superpose eq62 eq10
    | exact resolve eq10 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq62 x
       grind)
    | exact superpose eq62 eq43
    | exact resolve eq43 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq66 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq65
       have i₂ := eq62 sF2
       grind)
    | exact superpose eq62 eq65
    | exact resolve eq65 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq64
    | exact resolve eq64 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq73 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq62 sF2
       grind)
    | exact superpose eq62 eq49
    | exact resolve eq49 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq74 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq73
       have i₂ := eq62 x
       grind)
    | exact superpose eq62 eq73
    | exact resolve eq73 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq75 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (M.op y x) ∨ x = (k x y) := by
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
  have eq76 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq88
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq88
    | exact resolve eq88 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y x) := by
    first
    | exact superpose eq20 eq93
    | exact resolve eq93 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq96 : (M.op x x) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq95
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq95
    | exact resolve eq95 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq247 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq62 (τ X0)
       grind)
    | exact superpose eq62 eq34
    | exact resolve eq34 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq258 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq247 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq247
    | exact resolve eq247 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq259 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq258 X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq258
    | exact resolve eq258 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq325 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op X0 X1) (M.op X0 X1)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq327 : (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) y) := by
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq329 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ y)) := by
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq331 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq333 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq337 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq333 X0 X1
       have i₂ := eq52 (M.op X0 X0) X1
       grind)
    | exact superpose eq52 eq333
    | exact resolve eq333 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq340 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq329
       have i₂ := eq52 sF4 sF4
       grind)
    | exact superpose eq52 eq329
    | exact resolve eq329 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq342 : (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) y) := by
    first
    | (have i₁ := eq327
       have i₂ := eq52 sF0 sF0
       grind)
    | exact superpose eq52 eq327
    | exact resolve eq327 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq344 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq325 X0 X1
       have i₂ := eq52 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq52 eq325
    | exact resolve eq325 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq345 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) X0) X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq337 X0 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq337
    | exact resolve eq337 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq349 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq344 X0 X1
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq344
    | exact resolve eq344 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq353 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq331 (M.op X0 X1) X2
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq331
    | exact resolve eq331 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq331 X0 (M.op X0 X0)
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq331
    | exact resolve eq331 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq331 (σ X0) X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq331
    | exact resolve eq331 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0 X1
       have i₂ := eq52 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq52 eq59
    | (have j0 := eq59 X0 X1
       grind)
    | (have r₁ := eq59 (M.op (M.op X0 X0) X1) (M.op X0 X1)
       have r₂ := eq52 X0 X1
       grind)
    | (have r₁ := eq59 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) (M.op X0 X0)
       have r₂ := eq52 X0 (M.op X0 X0)
       grind)
    | exact resolve eq59 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq471 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op (M.op (M.op X0 X0) X1) (M.op X0 X1)) = (k X1 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq470 X0 X1
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq470
    | (have j0 := eq470 X0 X1
       grind)
    | (have r₁ := eq470 (M.op (M.op X0 X0) X1) (M.op X0 X1)
       have r₂ := eq52 X0 X1
       grind)
    | (have r₁ := eq470 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) (M.op X0 X0)
       have r₂ := eq52 X0 (M.op X0 X0)
       grind)
    | exact resolve eq470 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq537 : ∀ X0 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) (M.op (M.op X0 X0) X0)) = (k X0 (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0)) := by
    intro X0
    first
    | (have j0 := eq471 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq538 : ∀ X0 : G, (k X0 X0) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq537 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq537
    | exact resolve eq537 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq539 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq538 X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq538
    | exact resolve eq538 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq556 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq259 X0
       grind)
    | exact superpose eq259 eq16
    | exact resolve eq16 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq644 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq645 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq644 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq644
    | (have j0 := eq644 X0 X1
       grind)
    | exact resolve eq644 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq702 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq645 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq645
    | (have j0 := eq645 X0 y
       grind)
    | exact resolve eq645 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq829 : ∀ X0 : G, (τ X0) = (M.op (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq14 (τ X0) (τ X0)
       have i₂ := eq556 X0
       grind)
    | exact superpose eq556 eq14
    | exact resolve eq14 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq836 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op (M.op X0 X0) (M.op X0 X0))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq829 X0
       have i₂ := eq556 (M.op X0 X0)
       grind)
    | exact superpose eq556 eq829
    | exact resolve eq829 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq843 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op (M.op X0 X0) X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq836 X0
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq836
    | exact resolve eq836 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq850 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) (σ y)) := by
    first
    | exact superpose eq340 eq52
    | exact resolve eq52 eq340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq855 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq850
       have i₂ := eq52 (M.op sF4 sF4) sF4
       grind)
    | exact superpose eq52 eq850
    | exact resolve eq850 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq857 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq855
       have i₂ := eq14 sF4 sF4
       grind)
    | exact superpose eq14 eq855
    | exact resolve eq855 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq858 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq857
       have i₂ := eq52 sF2 sF2
       grind)
    | exact superpose eq52 eq857
    | exact resolve eq857 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq859 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) (M.op (M.op (M.op x y) (M.op x y)) (M.op x y))) y) := by
    first
    | exact superpose eq342 eq52
    | exact resolve eq52 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq864 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op x y)) y) := by
    first
    | (have i₁ := eq859
       have i₂ := eq52 (M.op sF0 sF0) sF0
       grind)
    | exact superpose eq52 eq859
    | exact resolve eq859 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq866 : (M.op (M.op x y) y) = (M.op (M.op x x) (M.op x x)) := by
    first
    | (have i₁ := eq864
       have i₂ := eq14 sF0 sF0
       grind)
    | exact superpose eq14 eq864
    | exact resolve eq864 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864
  have eq867 : (M.op (M.op x y) y) = (M.op (M.op x x) x) := by
    first
    | (have i₁ := eq866
       have i₂ := eq52 x x
       grind)
    | exact superpose eq52 eq866
    | exact resolve eq866 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq883 : x = (M.op (M.op (M.op x y) y) x) := by
    first
    | (have i₁ := eq331 x x
       have i₂ := eq867
       grind)
    | exact superpose eq867 eq331
    | exact resolve eq331 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq897 : (M.op x x) = (M.op x (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq539 x
       have i₂ := eq867
       grind)
    | exact superpose eq867 eq539
    | exact resolve eq539 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539 eq867
  have eq911 : x ≠ (M.op x x) ∨ (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = (k x (M.op (M.op x y) y)) := by
    first
    | exact superpose eq883 eq13
    | (have j0 := eq13 x (M.op (M.op x y) y)
       grind)
    | exact resolve eq13 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq913 : (M.op (M.op (M.op x y) (M.op x y)) y) = (k x (M.op (M.op x y) y)) ∨ x ≠ (M.op x x) := by
    first
    | (have i₁ := eq911
       have i₂ := eq52 sF0 y
       grind)
    | exact superpose eq52 eq911
    | exact resolve eq911 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq915 : x ≠ (M.op x x) ∨ x = (k x (M.op (M.op x y) y)) := by
    first
    | exact superpose eq50 eq913
    | exact resolve eq913 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq913
  have eq917 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op (M.op (M.op x y) y) x) ∨ x = (k x (M.op (M.op x y) y)) := by
    first
    | exact superpose eq897 eq12
    | (have j0 := eq12 x (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq12 x (M.op (M.op x y) y)
       have r₂ := eq897
       grind)
    | exact resolve eq12 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq919 : (M.op x x) = (M.op (M.op (M.op x y) y) x) ∨ x = (k x (M.op (M.op x y) y)) := by grind
  clear eq917
  have eq921 : x = (M.op x x) ∨ x = (k x (M.op (M.op x y) y)) := by
    first
    | exact superpose eq883 eq919
    | exact resolve eq919 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883 eq919
  have eq987 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq858 eq355
    | exact resolve eq355 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355 eq858
  have eq3146 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq345 (σ X0) (σ X0)
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq345
    | exact resolve eq345 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq3168 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3146 X0
       have i₂ := eq412 X0 (σ X0)
       grind)
    | exact superpose eq412 eq3146
    | exact resolve eq3146 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412 eq3146
  have eq3377 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op X0 X1)) (M.op (M.op (M.op X0 X0) X1) (M.op X0 X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op (M.op X0 X0) X1) (M.op X0 X1)) X1
       have i₂ := eq349 X0 X1
       grind)
    | exact superpose eq349 eq52
    | exact resolve eq52 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq3382 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3377 X0 X1
       have i₂ := eq52 (M.op (M.op X0 X0) X1) (M.op X0 X1)
       grind)
    | exact superpose eq52 eq3377
    | exact resolve eq3377 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3377
  have eq3429 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3382 X0 X1
       have i₂ := eq52 (M.op X0 X0) X1
       grind)
    | exact superpose eq52 eq3382
    | exact resolve eq3382 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3382
  have eq3466 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3429 X1 X1
       have i₂ := eq52 X1 X1
       grind)
    | exact superpose eq52 eq3429
    | exact resolve eq3429 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3429
  have eq3490 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3466 X0 X1
       have i₂ := eq345 X0 X1
       grind)
    | exact superpose eq345 eq3466
    | exact resolve eq3466 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq3466
  have eq6096 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq702 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq702
    | (have j0 := eq702 x
       grind)
    | exact resolve eq702 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq6125 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq6096
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq6096
    | exact resolve eq6096 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6096
  have eq6143 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq6125
    | exact resolve eq6125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6125
  have eq6153 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq6143
       have i₂ := eq66
       grind)
    | exact superpose eq66 eq6143
    | exact resolve eq6143 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6143
  have eq6161 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq6153
    | exact resolve eq6153 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6153
  have eq6169 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq6161
       have i₂ := eq66
       grind)
    | exact superpose eq66 eq6161
    | exact resolve eq6161 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6161
  have eq15844 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op (M.op X0 X1) X1)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq843 X0
       have i₂ := eq3490 X0 X1
       grind)
    | (have i₁ := eq843 X1
       have i₂ := eq3490 X1 X1
       grind)
    | exact superpose eq3490 eq843
    | exact resolve eq843 eq3490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq16407 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq353 X0 X0 X2
       have i₂ := eq3490 X0 X1
       grind)
    | (have i₁ := eq353 X1 X1 X2
       have i₂ := eq3490 X1 X1
       grind)
    | exact superpose eq3490 eq353
    | exact resolve eq353 eq3490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3490
  have eq20737 : x = (k x (M.op (M.op x y) y)) := by
    first
    | (have r₁ := eq921
       have r₂ := eq915
       grind)
    | exact resolve eq921 eq915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915 eq921
  have eq34743 : y = (M.op (M.op (M.op x x) (M.op x x)) x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq14
    | exact resolve eq14 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq34775 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq34743
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq34743
    | exact resolve eq34743 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34743
  have eq34797 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq34775 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq34775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34798 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq34797
    | exact resolve eq34797 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34797
  have eq34809 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq34798
       have r₂ := eq27
       grind)
    | exact resolve eq34798 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34798
  have eq34813 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq34809
    | exact resolve eq34809 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34809
  have eq34835 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (σ x)) X0) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq34813 eq16407
    | exact resolve eq16407 eq34813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34813
  have eq34839 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq34835 x
       have i₂ := eq353 sF2 sF2 x
       grind)
    | exact superpose eq353 eq34835
    | exact resolve eq34835 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34835
  have eq37204 : (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq6169 eq14
    | exact resolve eq14 eq6169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6169
  have eq37237 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq37204
       have i₂ := eq14 sF2 sF2
       grind)
    | exact superpose eq14 eq37204
    | exact resolve eq37204 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37204
  have eq51783 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (σ y)) X0) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq34839 eq16407
    | exact resolve eq16407 eq34839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34839
  have eq51788 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq51783 x
       have i₂ := eq353 sF2 sF3 x
       grind)
    | exact superpose eq353 eq51783
    | exact resolve eq51783 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353 eq51783
  have eq51845 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq51788
    | exact resolve eq51788 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51788
  have eq51846 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq51845
  have eq51875 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq51846 eq76
    | (have r₁ := eq76
       have r₂ := eq51846
       grind)
    | exact resolve eq76 eq51846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq51948 : (τ (σ x)) = (M.op (τ (M.op (M.op (σ x) (σ y)) (σ x))) (τ (σ x))) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq51846 eq15844
    | exact resolve eq15844 eq51846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15844 eq51846
  have eq51952 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq51875
  have eq51953 : x = (M.op (τ (M.op (M.op (σ x) (σ y)) (σ x))) x) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq28 eq51948
    | exact resolve eq51948 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51948
  have eq60660 : ∀ X0 : G, (M.op (M.op (M.op x x) X0) X0) = (M.op (τ (M.op (M.op (σ x) (σ y)) (σ x))) (τ (M.op (M.op (σ x) (σ y)) (σ x)))) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq51953 eq16407
    | exact resolve eq16407 eq51953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16407 eq51953
  have eq60664 : ∀ X0 : G, (M.op (M.op (M.op x x) X0) X0) = (τ (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (σ x)))) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq60660 X0
       have i₂ := eq556 (M.op sF4 sF2)
       grind)
    | exact superpose eq556 eq60660
    | exact resolve eq60660 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556 eq60660
  have eq60683 : ∀ X0 : G, (M.op (M.op (M.op x x) X0) X0) = (τ (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x))) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq60664 X0
       have i₂ := eq52 sF4 sF2
       grind)
    | exact superpose eq52 eq60664
    | exact resolve eq60664 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq60664
  have eq60699 : x = (τ (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x))) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq60683 x
       have i₂ := eq331 x x
       grind)
    | exact superpose eq331 eq60683
    | exact resolve eq60683 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331 eq60683
  have eq98387 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq51952 eq14
    | exact resolve eq14 eq51952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51952
  have eq1399458 : x = (τ (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq98387 eq60699
    | exact resolve eq60699 eq98387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60699 eq98387
  have eq1399617 : x = (τ (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq1399458
  have eq1399691 : x = y ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq1399617
    | exact resolve eq1399617 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399617
  have eq1399692 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq1399691
  have eq1402365 : (τ (σ x)) = (k x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq1399692 eq58
    | exact resolve eq58 eq1399692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq1402376 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq1399692 eq34775
    | exact resolve eq34775 eq1399692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34775 eq1399692
  have eq1402429 : (M.op x y) = (M.op x x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1402376
  have eq1402452 : (M.op x y) = (M.op x x) ∨ x = (k x y) ∨ x = y := by
    first
    | exact superpose eq28 eq1402365
    | exact resolve eq1402365 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402365
  have eq1402469 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq66
       have i₂ := eq1402429
       grind)
    | exact superpose eq1402429 eq66
    | exact resolve eq66 eq1402429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1402521 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3168 x
       have i₂ := eq1402429
       grind)
    | exact superpose eq1402429 eq3168
    | exact resolve eq3168 eq1402429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3168 eq1402429
  have eq1402720 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq1402521
    | exact resolve eq1402521 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402521
  have eq1402740 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq1402469
    | exact resolve eq1402469 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402469
  have eq1402795 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1402720
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1402720
    | exact resolve eq1402720 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402720
  have eq1415140 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1402740 eq987
    | exact resolve eq987 eq1402740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq1426073 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (k x y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq75
       have i₂ := eq1402452
       grind)
    | exact superpose eq1402452 eq75
    | (have r₁ := eq75
       have r₂ := eq1402452
       grind)
    | exact resolve eq75 eq1402452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq1426217 : x = (M.op (M.op (M.op x y) (M.op x y)) x) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq1402452
       grind)
    | exact superpose eq1402452 eq14
    | exact resolve eq14 eq1402452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402452
  have eq1426252 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (k x y) ∨ x = y := by grind
  clear eq1426073
  have eq1426253 : (M.op x y) = (M.op y x) ∨ x = (k x y) ∨ x = y := by grind
  clear eq1426252
  have eq1450825 : y = (M.op (M.op (M.op x y) (M.op x y)) x) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq1426253
       grind)
    | exact superpose eq1426253 eq14
    | exact resolve eq14 eq1426253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426253
  have eq1718713 : x = y ∨ x = (k x y) ∨ x = y ∨ x = (k x y) ∨ x = y := by
    first
    | exact superpose eq1450825 eq1426217
    | exact resolve eq1426217 eq1450825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426217 eq1450825
  have eq1718778 : x = (k x y) ∨ x = y := by grind
  clear eq1718713
  have eq1719001 : (σ x) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq1718778
       grind)
    | exact superpose eq1718778 eq44
    | exact resolve eq44 eq1718778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1718778
  have eq1719195 : (σ x) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1719001
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1719001
    | exact resolve eq1719001 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719001
  have eq1720692 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq37237 eq1719195
    | exact resolve eq1719195 eq37237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37237 eq1719195
  have eq1747207 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1720692 eq1402740
    | exact resolve eq1402740 eq1720692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402740
  have eq1747395 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq1747207
  have eq1747593 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1747395
       have r₂ := eq27
       grind)
    | exact resolve eq1747395 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1747395
  have eq1749061 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1747593 eq1415140
    | exact resolve eq1415140 eq1747593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1415140
  have eq1749078 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq1749061
  have eq1750477 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq1749078
    | exact resolve eq1749078 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1749078
  have eq1805133 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1747593 eq1750477
    | exact resolve eq1750477 eq1747593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1747593 eq1750477
  have eq1805250 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq1805133
  have eq1836830 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1805250 eq1402795
    | exact resolve eq1402795 eq1805250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402795 eq1805250
  have eq1836898 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1836830
  have eq1836918 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1836898 eq29
    | exact resolve eq29 eq1836898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1838026 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq28 eq1836918
    | exact resolve eq1836918 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836918
  have eq1838027 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq1838026
  have eq1838096 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1838027 eq28
    | exact resolve eq28 eq1838027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1838027
  have eq1840782 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq1838096
    | exact resolve eq1838096 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1838096
  have eq1841056 : x = (k x (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1840782 eq20737
    | exact resolve eq20737 eq1840782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20737
  have eq1841383 : x = (k x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq1841056
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1841056
    | exact resolve eq1841056 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1841056
  have eq1841776 : x = (k x x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1840782 eq1841383
    | exact resolve eq1841383 eq1840782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1840782 eq1841383
  have eq1841877 : x = (k x x) ∨ x = y := by grind
  clear eq1841776
  have eq1841973 : x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq1841877
       have i₂ := eq62 x
       grind)
    | exact superpose eq62 eq1841877
    | exact resolve eq1841877 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq1841877
  have eq1845660 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq66
       have i₂ := eq1841973
       grind)
    | exact superpose eq1841973 eq66
    | exact resolve eq66 eq1841973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq1841973
  have eq1846092 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq1845660
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1845660
    | exact resolve eq1845660 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1845660
  have eq1852350 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1846092 eq1720692
    | exact resolve eq1720692 eq1846092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1720692 eq1846092
  have eq1852540 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1852350
  have eq1861255 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1852540 eq27
    | exact resolve eq27 eq1852540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1852540
  have eq1865337 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1861255
       have r₂ := eq1836898
       grind)
    | exact resolve eq1861255 eq1836898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836898 eq1861255
  have eq1866336 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1865337 eq29
    | exact resolve eq29 eq1865337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1865337
  have eq1867482 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq1866336
    | exact resolve eq1866336 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1866336
  have eq1867483 : x = y := by grind
  clear eq1867482
  have eq1867556 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1867483
       grind)
    | exact superpose eq1867483 eq18
    | exact resolve eq18 eq1867483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1867557 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1867483
       grind)
    | exact superpose eq1867483 eq24
    | exact resolve eq24 eq1867483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1867483
  have eq1867970 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1867557
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1867557
    | exact resolve eq1867557 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1867557
  have eq1868019 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1867970 eq26
    | exact resolve eq26 eq1867970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1867970
  have eq1869488 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1868019 eq74
    | exact resolve eq74 eq1868019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq1868019
  have eq1869934 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1869488
       have i₂ := eq1867556
       grind)
    | exact superpose eq1867556 eq1869488
    | exact resolve eq1869488 eq1867556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1867556 eq1869488
  have eq1872041 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1869934 eq15
    | exact resolve eq15 eq1869934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869934
  have eq1872862 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1872041
    | exact resolve eq1872041 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1872041
  have eq1873035 : False := by grind
  exact eq1873035

/-- `Equation2663`: `x = ((x ◇ y) ◇ (x ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(Y,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pyx_pyy_pxy_y_pyx_Equation2663 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2663 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2663.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
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
  have eq28 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq37 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35
    | (have j0 := eq35 x
       grind)
    | exact resolve eq35 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq49 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq59 (σ X0)
       grind)
    | exact superpose eq59 eq10
    | exact resolve eq10 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq59 x
       grind)
    | exact superpose eq59 eq43
    | exact resolve eq43 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq63 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq62
       have i₂ := eq59 sF2
       grind)
    | exact superpose eq59 eq62
    | exact resolve eq62 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq64 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq61
    | exact resolve eq61 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq70 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq59 sF2
       grind)
    | exact superpose eq59 eq49
    | exact resolve eq49 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq70
       have i₂ := eq59 x
       grind)
    | exact superpose eq59 eq70
    | exact resolve eq70 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq72 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq95 : (k (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq100 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq96
       have i₂ := eq59 sF3
       grind)
    | exact superpose eq59 eq96
    | exact resolve eq96 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq102 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq100
       have i₂ := eq59 y
       grind)
    | exact superpose eq59 eq100
    | exact resolve eq100 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq111 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq114 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq111
       have i₂ := eq59 sF1
       grind)
    | exact superpose eq59 eq111
    | exact resolve eq111 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq116 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq114
       have i₂ := eq59 sF0
       grind)
    | exact superpose eq59 eq114
    | exact resolve eq114 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq95
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq95 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq95
       grind)
    | exact superpose eq95 eq16
    | exact resolve eq16 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq118
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq118
    | exact resolve eq118 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq126 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq20 eq125
    | exact resolve eq125 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq127 : (M.op x x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq126
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq126
    | exact resolve eq126 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq174 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq116 eq16
    | exact resolve eq16 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq242 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq59 (τ X0)
       grind)
    | exact superpose eq59 eq34
    | exact resolve eq34 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq253 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq242 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq242
    | exact resolve eq242 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq254 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq253 X0
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq253
    | exact resolve eq253 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq253
  have eq318 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op X0 X1) (M.op X0 X1)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) y) := by
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq322 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ y)) := by
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq329 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq325 X0 X1
       have i₂ := eq52 (M.op X0 X0) X1
       grind)
    | exact superpose eq52 eq325
    | exact resolve eq325 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq331 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq322
       have i₂ := eq52 sF4 sF4
       grind)
    | exact superpose eq52 eq322
    | exact resolve eq322 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq333 : (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) y) := by
    first
    | (have i₁ := eq320
       have i₂ := eq52 sF0 sF0
       grind)
    | exact superpose eq52 eq320
    | exact resolve eq320 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq335 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq318 X0 X1
       have i₂ := eq52 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq52 eq318
    | exact resolve eq318 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq336 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) X0) X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq329 X0 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq329
    | exact resolve eq329 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq340 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq335 X0 X1
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq335
    | exact resolve eq335 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq344 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq324 (M.op X0 X1) X2
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq324
    | exact resolve eq324 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq324 X0 (M.op X0 X0)
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq324
    | exact resolve eq324 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq390 : (σ (M.op (k y x) (k y x))) = (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq64 (k y x)
       have i₂ := eq95
       grind)
    | exact superpose eq95 eq64
    | exact resolve eq64 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq398 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq14 (σ X0) (σ X0)
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq14
    | exact resolve eq14 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq400 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq324 (σ X0) X1
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq324
    | exact resolve eq324 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq404 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq398 X0
       have i₂ := eq64 (M.op X0 X0)
       grind)
    | exact superpose eq64 eq398
    | exact resolve eq398 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq411 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq404 X0
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq404
    | exact resolve eq404 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq459 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 X1
       have i₂ := eq64 X1
       grind)
    | exact superpose eq64 eq81
    | (have j0 := eq81 X0 X1
       grind)
    | exact resolve eq81 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq460 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq459 X0 X1
       have i₂ := eq64 X1
       grind)
    | exact superpose eq64 eq459
    | (have j0 := eq459 X0 X1
       grind)
    | exact resolve eq459 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq461 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq460 X0 X1
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq460
    | (have j0 := eq460 X0 X1
       grind)
    | exact resolve eq460 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq539 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ X0)) ∨ (σ (M.op x x)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq461 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq461
    | (have j0 := eq461 X0 x
       grind)
    | exact resolve eq461 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq577 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (σ X0)) ∨ (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ (M.op x x)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq539 X0
       have i₂ := eq63
       grind)
    | exact superpose eq63 eq539
    | (have j0 := eq539 X0
       grind)
    | exact resolve eq539 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq590 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ x) (σ x)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq577 X0
       have i₂ := eq63
       grind)
    | exact superpose eq63 eq577
    | (have j0 := eq577 X0
       grind)
    | exact resolve eq577 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq626 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq254 X0
       grind)
    | exact superpose eq254 eq16
    | exact resolve eq16 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq743 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) (σ y)) := by
    first
    | exact superpose eq331 eq52
    | exact resolve eq52 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq746 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq743
       have i₂ := eq52 (M.op sF4 sF4) sF4
       grind)
    | exact superpose eq52 eq743
    | exact resolve eq743 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq747 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq746
       have i₂ := eq14 sF4 sF4
       grind)
    | exact superpose eq14 eq746
    | exact resolve eq746 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq748 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq747
       have i₂ := eq52 sF2 sF2
       grind)
    | exact superpose eq52 eq747
    | exact resolve eq747 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq798 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) (M.op (M.op (M.op x y) (M.op x y)) (M.op x y))) y) := by
    first
    | exact superpose eq333 eq52
    | exact resolve eq52 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq801 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op x y)) y) := by
    first
    | (have i₁ := eq798
       have i₂ := eq52 (M.op sF0 sF0) sF0
       grind)
    | exact superpose eq52 eq798
    | exact resolve eq798 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq802 : (M.op (M.op x y) y) = (M.op (M.op x x) (M.op x x)) := by
    first
    | (have i₁ := eq801
       have i₂ := eq14 sF0 sF0
       grind)
    | exact superpose eq14 eq801
    | exact resolve eq801 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq803 : (M.op (M.op x y) y) = (M.op (M.op x x) x) := by
    first
    | (have i₁ := eq802
       have i₂ := eq52 x x
       grind)
    | exact superpose eq52 eq802
    | exact resolve eq802 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq813 : (M.op (M.op x x) (M.op x x)) = (τ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq71 eq626
    | exact resolve eq626 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq841 : (M.op (M.op x x) (M.op x x)) = (τ (M.op (M.op (σ x) (σ x)) (σ x))) := by
    first
    | (have i₁ := eq813
       have i₂ := eq52 sF2 sF2
       grind)
    | exact superpose eq52 eq813
    | exact resolve eq813 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813
  have eq846 : (M.op (M.op x x) (M.op x x)) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq748 eq841
    | exact resolve eq841 eq748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq847 : (M.op (M.op x x) x) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq846
       have i₂ := eq52 x x
       grind)
    | exact superpose eq52 eq846
    | exact resolve eq846 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq848 : (M.op (M.op x y) y) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq847
       have i₂ := eq803
       grind)
    | exact superpose eq803 eq847
    | exact resolve eq847 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803 eq847
  have eq897 : (σ (M.op (M.op x y) y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq848 eq15
    | exact resolve eq15 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq1002 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq748 eq346
    | exact resolve eq346 eq748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346 eq748
  have eq2943 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op (M.op X0 X1) (M.op X0 X1))) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq336 (M.op (M.op X0 X1) (M.op X0 X1)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq336
    | exact resolve eq336 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2964 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq336 (σ X0) (σ X0)
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq336
    | exact resolve eq336 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq2983 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2964 X0
       have i₂ := eq400 X0 (σ X0)
       grind)
    | exact superpose eq400 eq2964
    | exact resolve eq2964 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400 eq2964
  have eq3003 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2943 X0 X1
       have i₂ := eq324 (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))
       grind)
    | exact superpose eq324 eq2943
    | exact resolve eq2943 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2943
  have eq3179 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op X0 X1)) (M.op (M.op (M.op X0 X0) X1) (M.op X0 X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op (M.op X0 X0) X1) (M.op X0 X1)) X1
       have i₂ := eq340 X0 X1
       grind)
    | exact superpose eq340 eq52
    | exact resolve eq52 eq340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq3182 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3179 X0 X1
       have i₂ := eq52 (M.op (M.op X0 X0) X1) (M.op X0 X1)
       grind)
    | exact superpose eq52 eq3179
    | exact resolve eq3179 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3179
  have eq3227 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3182 X0 X1
       have i₂ := eq52 (M.op X0 X0) X1
       grind)
    | exact superpose eq52 eq3182
    | exact resolve eq3182 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3182
  have eq3263 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3227 X1 X1
       have i₂ := eq52 X1 X1
       grind)
    | exact superpose eq52 eq3227
    | exact resolve eq3227 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3227
  have eq3286 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3263 X0 X1
       have i₂ := eq336 X0 X1
       grind)
    | exact superpose eq336 eq3263
    | exact resolve eq3263 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336 eq3263
  have eq4711 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq590 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq590
    | (have j0 := eq590 y
       grind)
    | exact resolve eq590 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq4735 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4711
       have i₂ := eq95
       grind)
    | exact superpose eq95 eq4711
    | exact resolve eq4711 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4711
  have eq4753 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
    first
    | exact superpose eq26 eq4735
    | exact resolve eq4735 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4735
  have eq4761 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
    first
    | exact superpose eq26 eq4753
    | exact resolve eq4753 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4753
  have eq4766 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq4761
       have i₂ := eq102
       grind)
    | exact superpose eq102 eq4761
    | exact resolve eq4761 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq4761
  have eq8149 : (σ y) = (M.op (σ (M.op (M.op y y) y)) (σ y)) := by
    first
    | (have i₁ := eq411 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq411
    | (have j0 := eq411 y
       grind)
    | exact resolve eq411 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq411
  have eq8462 : ∀ X0 : G, (σ y) = (M.op (σ (M.op (M.op y X0) X0)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq8149
       have i₂ := eq3286 y X0
       grind)
    | (have i₁ := eq8149
       have i₂ := eq3286 y y
       grind)
    | exact superpose eq3286 eq8149
    | exact resolve eq8149 eq3286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8149
  have eq15319 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq344 X0 X0 X2
       have i₂ := eq3286 X0 X1
       grind)
    | (have i₁ := eq344 X1 X1 X2
       have i₂ := eq3286 X1 X1
       grind)
    | exact superpose eq3286 eq344
    | exact resolve eq344 eq3286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3286
  have eq31679 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x x) y) X0) X0) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq15319 y y x
       have i₂ := eq127
       grind)
    | exact superpose eq127 eq15319
    | exact resolve eq15319 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq31680 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq31679 x
       have i₂ := eq344 x y x
       grind)
    | exact superpose eq344 eq31679
    | exact resolve eq31679 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31679
  have eq31727 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq31680
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq31680
    | exact resolve eq31680 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31680
  have eq31728 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq31727
  have eq31769 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq31728 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq31728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31770 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq31769
    | exact resolve eq31769 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31769
  have eq31781 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq31770
       have r₂ := eq27
       grind)
    | exact resolve eq31770 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31770
  have eq31785 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq31781
    | exact resolve eq31781 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31781
  have eq31851 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (σ y)) X0) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq31785 eq15319
    | exact resolve eq15319 eq31785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31785
  have eq31852 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq31851 x
       have i₂ := eq344 sF2 sF3 x
       grind)
    | exact superpose eq344 eq31851
    | exact resolve eq31851 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31851
  have eq31900 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq31852
    | exact resolve eq31852 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31852
  have eq31901 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq31900
  have eq31925 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq31901 eq73
    | (have r₁ := eq73
       have r₂ := eq31901
       grind)
    | exact resolve eq73 eq31901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq31993 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq31925
  have eq33910 : (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (σ y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq4766 eq3003
    | exact resolve eq3003 eq4766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3003 eq4766
  have eq33931 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq33910
       have i₂ := eq324 sF2 sF3
       grind)
    | exact superpose eq324 eq33910
    | exact resolve eq33910 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33910
  have eq67663 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq31993 eq14
    | exact resolve eq14 eq31993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31993
  have eq67689 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq51 eq67663
    | exact resolve eq67663 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67663
  have eq67709 : (τ (σ x)) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq67689 eq124
    | exact resolve eq124 eq67689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq67689
  have eq67730 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | exact superpose eq28 eq67709
    | exact resolve eq67709 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67709
  have eq68327 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq67730
       grind)
    | exact superpose eq67730 eq72
    | (have r₁ := eq72
       have r₂ := eq67730
       grind)
    | exact resolve eq72 eq67730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq67730
  have eq68403 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq68327
  have eq68404 : (M.op x y) = (M.op y y) ∨ x = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq68403
  have eq69178 : (σ y) = (M.op (σ (M.op (M.op x y) y)) (σ y)) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8462 y
       have i₂ := eq68404
       grind)
    | exact superpose eq68404 eq8462
    | exact resolve eq8462 eq68404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8462 eq68404
  have eq69251 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq897 eq69178
    | exact resolve eq69178 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69178
  have eq132220 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (M.op (σ y) (σ y)) X0) X0) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq69251 eq15319
    | exact resolve eq15319 eq69251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15319 eq69251
  have eq132225 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq132220 x
       have i₂ := eq324 sF3 x
       grind)
    | exact superpose eq324 eq132220
    | exact resolve eq132220 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132220
  have eq132246 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq132225
       have i₂ := eq52 sF4 sF3
       grind)
    | exact superpose eq52 eq132225
    | exact resolve eq132225 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq132225
  have eq132257 : (σ x) = (σ y) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq51 eq132246
    | exact resolve eq132246 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq132246
  have eq132258 : x = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq132257
  have eq132267 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq132258
       grind)
    | exact superpose eq132258 eq95
    | exact resolve eq95 eq132258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq132274 : (σ (M.op x x)) = (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq390
       have i₂ := eq132258
       grind)
    | exact superpose eq132258 eq390
    | exact resolve eq390 eq132258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390 eq132258
  have eq132295 : (M.op (σ x) (σ x)) = (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq132274
       have i₂ := eq63
       grind)
    | exact superpose eq63 eq132274
    | exact resolve eq132274 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132274
  have eq132302 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq132267
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq132267
    | exact resolve eq132267 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132267
  have eq138012 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq31728 eq132295
    | exact resolve eq132295 eq31728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138028 : ∀ X0 X1 : G, (M.op (k (σ y) (σ x)) X0) = (M.op (M.op (M.op (M.op (σ x) (σ x)) X0) X1) X1) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq132295 eq344
    | exact resolve eq344 eq132295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132295
  have eq138109 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (k (σ y) (σ x)) X0) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq138028 x x
       have i₂ := eq344 sF2 x x
       grind)
    | exact superpose eq344 eq138028
    | exact resolve eq138028 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138028
  have eq139155 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x y)) X0) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq31728 eq138109
    | exact resolve eq138109 eq31728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31728 eq138109
  have eq263498 : (M.op x x) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq138012 eq71
    | exact resolve eq71 eq138012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq263517 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq138012 eq31901
    | exact resolve eq31901 eq138012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31901 eq138012
  have eq263700 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq263517
  have eq263747 : (M.op (M.op x y) (M.op x y)) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq174 eq263498
    | exact resolve eq263498 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq263498
  have eq264351 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq263700 eq324
    | exact resolve eq324 eq263700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324 eq263700
  have eq308635 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq139155
    | (have j0 := eq139155 (σ y)
       grind)
    | exact resolve eq139155 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139155
  have eq312760 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op (M.op x x) X0) X1) X1) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq263747 eq344
    | exact resolve eq344 eq263747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263747
  have eq312911 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq312760 X0 x
       have i₂ := eq344 x X0 x
       grind)
    | exact superpose eq344 eq312760
    | exact resolve eq312760 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344 eq312760
  have eq365075 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq312911 eq897
    | exact resolve eq897 eq312911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897 eq312911
  have eq365613 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq365075
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq365075
    | exact resolve eq365075 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365075
  have eq365648 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq365613
    | exact resolve eq365613 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365613
  have eq367460 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq365648 eq264351
    | exact resolve eq264351 eq365648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264351 eq365648
  have eq367485 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq367460
  have eq376240 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq367485 eq308635
    | exact resolve eq308635 eq367485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308635 eq367485
  have eq376290 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq376240
  have eq376293 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq376290
       have r₂ := eq27
       grind)
    | exact resolve eq376290 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376290
  have eq376297 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq63
       have i₂ := eq376293
       grind)
    | exact superpose eq376293 eq63
    | exact resolve eq63 eq376293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376357 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2983 x
       have i₂ := eq376293
       grind)
    | exact superpose eq376293 eq2983
    | exact resolve eq2983 eq376293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2983 eq376293
  have eq376471 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq376357
    | exact resolve eq376357 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376357
  have eq376492 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq376297
    | exact resolve eq376297 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376297
  have eq376506 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq376471
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq376471
    | exact resolve eq376471 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq376471
  have eq378096 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq376492 eq1002
    | exact resolve eq1002 eq376492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002
  have eq1792688 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq33931 eq132302
    | exact resolve eq132302 eq33931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33931 eq132302
  have eq1792958 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1792688
  have eq1793110 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1792958 eq376492
    | exact resolve eq376492 eq1792958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376492 eq1792958
  have eq1793409 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1793110
  have eq1793498 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1793409
       have r₂ := eq27
       grind)
    | exact resolve eq1793409 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1793409
  have eq1793520 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1793498 eq27
    | exact resolve eq27 eq1793498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1793784 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1793498 eq378096
    | exact resolve eq378096 eq1793498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378096
  have eq1793983 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by grind
  clear eq1793784
  have eq1794115 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq1793983
    | exact resolve eq1793983 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1793983
  have eq1795480 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1793498 eq1794115
    | exact resolve eq1794115 eq1793498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1793498 eq1794115
  have eq1795528 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) := by grind
  clear eq1795480
  have eq1798645 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1795528 eq376506
    | exact resolve eq376506 eq1795528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376506 eq1795528
  have eq1798854 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq1798645
  have eq1798955 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1798854
       have r₂ := eq1793520
       grind)
    | exact resolve eq1798854 eq1793520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1793520 eq1798854
  have eq1799001 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1798955 eq26
    | exact resolve eq26 eq1798955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1799002 : y = (τ (σ x)) := by
    first
    | exact superpose eq1798955 eq29
    | exact resolve eq29 eq1798955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1798955
  have eq1799306 : x = y := by
    first
    | exact superpose eq28 eq1799002
    | exact resolve eq1799002 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1799002
  have eq1799380 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1799306
       grind)
    | exact superpose eq1799306 eq18
    | exact resolve eq18 eq1799306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1799306
  have eq1800752 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq63
       have i₂ := eq1799380
       grind)
    | exact superpose eq1799380 eq63
    | exact resolve eq63 eq1799380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1799380
  have eq1801104 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1799001 eq1800752
    | exact resolve eq1800752 eq1799001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1799001 eq1800752
  have eq1801180 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1801104
    | exact resolve eq1801104 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1801104
  have eq1801231 : False := by grind
  exact eq1801231

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(Y,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pyx_pyy_pyx_y_pyx_Equation2666 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
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
  have eq28 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq22
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
  clear eq24
  have eq37 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35
    | (have j0 := eq35 x
       grind)
    | exact resolve eq35 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq50 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, x = (M.op (M.op (M.op x X0) (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq43
    | exact resolve eq43 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq72 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq69
    | exact resolve eq69 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq77 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (M.op y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (k (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq102 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq16
    | exact resolve eq16 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq85 y x
       grind)
    | exact superpose eq85 eq91
    | (have j1 := eq85 y x
       grind)
    | exact resolve eq91 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq114
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114
    | exact resolve eq114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq120
    | exact resolve eq120 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq121
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq121
    | exact resolve eq121 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq144 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq147 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq144
       have i₂ := eq66 sF1
       grind)
    | exact superpose eq66 eq144
    | exact resolve eq144 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq149 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq147
       have i₂ := eq66 sF0
       grind)
    | exact superpose eq66 eq147
    | exact resolve eq147 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq147
  have eq170 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq149 eq16
    | exact resolve eq16 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq235 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq239 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq633 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op (M.op x X0) (M.op x y)) X1)) = (M.op (M.op (M.op (M.op x X0) (M.op x y)) (M.op (M.op x (M.op (M.op (M.op x X0) (M.op x y)) X1)) X2)) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq651 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X1 X2 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X2)) (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X2)) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X2)) X3) X1
       have i₂ := eq52 X0 (M.op X0 X1) X2 X3
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq653 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x (M.op x y)) (M.op x X0)) (M.op (M.op (M.op x (M.op x y)) (M.op x X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op (M.op x sF0) (M.op x x)) x)
       have i₂ := eq52 x sF0 x x
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq53
  have eq775 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq122 eq85
    | (have j0 := eq85 (σ y) (σ x)
       grind)
    | exact resolve eq85 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq776 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq775
    | exact resolve eq775 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq779 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq776
       have r₂ := eq27
       grind)
    | exact resolve eq776 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq781 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq779
    | exact resolve eq779 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq783 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq781 eq78
    | (have r₁ := eq78
       have r₂ := eq781
       grind)
    | exact resolve eq78 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq797 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq783
  have eq937 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq797 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq944 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq937
       have r₂ := eq781
       grind)
    | exact resolve eq937 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781 eq937
  have eq945 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq944
    | exact resolve eq944 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq978 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq122 eq945
    | exact resolve eq945 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq980 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq945 eq122
    | exact resolve eq122 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq945
  have eq984 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq980
  have eq985 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq978
  have eq986 : (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq984
       have r₂ := eq27
       grind)
    | exact resolve eq984 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984
  have eq987 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq985
       have r₂ := eq27
       grind)
    | exact resolve eq985 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq990 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq987
       grind)
    | exact superpose eq987 eq72
    | exact resolve eq72 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq1006 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq990
    | exact resolve eq990 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq1153 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) X0)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1006 eq14
    | exact resolve eq14 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1154 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) X0) (σ (M.op x y))) X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1006 eq14
    | exact resolve eq14 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1159 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1006 eq651
    | exact resolve eq651 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1160 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1006 eq651
    | exact resolve eq651 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1172 : (τ (σ x)) = (k y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq986 eq102
    | exact resolve eq102 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq986
  have eq1178 : (M.op x y) = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq28 eq1172
    | exact resolve eq1172 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1172
  have eq1194 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq77
       have i₂ := eq1178
       grind)
    | exact superpose eq1178 eq77
    | (have r₁ := eq77
       have r₂ := eq1178
       grind)
    | exact resolve eq77 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1195 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq1178
       grind)
    | exact superpose eq1178 eq72
    | exact resolve eq72 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1211 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (k y x) := by grind
  clear eq1194
  have eq1212 : (M.op x y) = (M.op y x) ∨ x = (k y x) := by grind
  clear eq1211
  have eq1215 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (k y x) := by
    first
    | exact superpose eq20 eq1195
    | exact resolve eq1195 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195
  have eq1285 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1212
       grind)
    | exact superpose eq1212 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq1294 : (M.op x y) = (k y x) ∨ x = (k y x) := by
    first
    | (have r₁ := eq1285
       have r₂ := eq1178
       grind)
    | exact resolve eq1285 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178 eq1285
  have eq1295 : (M.op x y) = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq1294
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1294
    | exact resolve eq1294 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294
  have eq1320 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq1295
       grind)
    | exact superpose eq1295 eq91
    | exact resolve eq91 eq1295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295
  have eq1323 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | exact superpose eq20 eq1320
    | exact resolve eq1320 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320
  have eq1377 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (k y x) := by
    first
    | exact superpose eq1323 eq85
    | (have j0 := eq85 (σ y) (σ x)
       grind)
    | exact resolve eq85 eq1323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323
  have eq1378 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (k y x) := by
    first
    | exact superpose eq26 eq1377
    | exact resolve eq1377 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377
  have eq1381 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (k y x) := by
    first
    | (have r₁ := eq1378
       have r₂ := eq27
       grind)
    | exact resolve eq1378 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378
  have eq1383 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (k y x) := by
    first
    | exact superpose eq26 eq1381
    | exact resolve eq1381 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381
  have eq1387 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ x = (k y x) := by
    first
    | exact superpose eq1383 eq1215
    | exact resolve eq1215 eq1383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215 eq1383
  have eq1408 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by grind
  clear eq1387
  have eq1413 : x = (k y x) := by
    first
    | (have r₁ := eq1408
       have r₂ := eq27
       grind)
    | exact resolve eq1408 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1408
  have eq1465 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq91
       have i₂ := eq1413
       grind)
    | exact superpose eq1413 eq91
    | exact resolve eq91 eq1413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq1466 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq85 y x
       have i₂ := eq1413
       grind)
    | exact superpose eq1413 eq85
    | (have j0 := eq85 y x
       grind)
    | exact resolve eq85 eq1413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413
  have eq1467 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1466
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1466
    | exact resolve eq1466 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466
  have eq1468 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1465
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1465
    | exact resolve eq1465 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465
  have eq1470 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1467
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1467
    | exact resolve eq1467 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1467
  have eq1479 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1468 eq85
    | (have j0 := eq85 (σ y) (σ x)
       grind)
    | exact resolve eq85 eq1468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq1468
  have eq1480 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq1479
    | exact resolve eq1479 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479
  have eq1483 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1480
    | exact resolve eq1480 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1480
  have eq1539 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq1470
       grind)
    | exact superpose eq1470 eq72
    | exact resolve eq72 eq1470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq1470
  have eq1558 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1539
    | exact resolve eq1539 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1539
  have eq1615 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1483 eq1006
    | exact resolve eq1006 eq1483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1636 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1615
       have r₂ := eq27
       grind)
    | exact resolve eq1615 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1615
  have eq1641 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1636 eq239
    | exact resolve eq239 eq1636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq1713 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1558 eq1483
    | exact resolve eq1483 eq1558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1732 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1713
       have r₂ := eq27
       grind)
    | exact resolve eq1713 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1713
  have eq1789 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1732 eq27
    | exact resolve eq27 eq1732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1732
  have eq2047 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1558 eq1641
    | exact resolve eq1641 eq1558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1558
  have eq2051 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1006 eq1641
    | exact resolve eq1641 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1641
  have eq2062 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2051
  have eq2065 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2047
       have r₂ := eq1789
       grind)
    | exact resolve eq2047 eq1789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2047
  have eq3476 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1006 eq1153
    | exact resolve eq1153 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006 eq1153
  have eq3488 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3476
  have eq3596 : (M.op (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq1159
    | (have j0 := eq1159 (σ y)
       grind)
    | exact resolve eq1159 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159
  have eq3623 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ x)) (M.op (σ (M.op x y)) X0)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq3596 eq14
    | exact resolve eq14 eq3596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3596
  have eq3634 : (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3623 x
       have i₂ := eq651 sF1 sF2 x
       grind)
    | exact superpose eq651 eq3623
    | exact resolve eq3623 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3623
  have eq3704 : (M.op (σ (M.op x y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq1160
    | (have j0 := eq1160 (σ y)
       grind)
    | exact resolve eq1160 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq3713 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) X0) X0) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1160 eq1154
    | exact resolve eq1154 eq1160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154 eq1160
  have eq3724 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) X0) X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq3713 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3713
  have eq3731 : (M.op (σ (M.op x y)) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1636 eq3704
    | exact resolve eq3704 eq1636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1636 eq3704
  have eq3744 : (M.op (σ (M.op x y)) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3731
  have eq3801 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op (σ (M.op x y)) X0) X1)) = (M.op (M.op (M.op (σ (M.op x y)) X0) (M.op (σ (M.op x y)) X0)) X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq3724 eq651
    | exact resolve eq651 eq3724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3724
  have eq3808 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (M.op (σ (M.op x y)) X0) X1)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq3801 x X1
       have i₂ := eq14 sF1 x x
       grind)
    | exact superpose eq14 eq3801
    | exact resolve eq3801 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3801
  have eq4294 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3488 eq3634
    | exact resolve eq3634 eq3488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3488 eq3634
  have eq4307 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4294
  have eq4539 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq2062 eq3808
    | exact resolve eq3808 eq2062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3808
  have eq4601 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq4539 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4539
  have eq4620 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4307 eq4601
    | exact resolve eq4601 eq4307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4307 eq4601
  have eq4647 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4620
  have eq4777 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4647 eq3744
    | exact resolve eq3744 eq4647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3744 eq4647
  have eq4807 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4777
  have eq5029 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4807 eq2065
    | exact resolve eq2065 eq4807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2065
  have eq5030 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4807 eq2062
    | exact resolve eq2062 eq4807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2062 eq4807
  have eq5046 : (σ (M.op x y)) = (σ x) := by grind
  clear eq5030
  have eq5047 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq5029
  have eq5050 : x = (M.op x y) := by
    first
    | (have r₁ := eq5047
       have r₂ := eq1789
       grind)
    | exact resolve eq5047 eq1789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1789 eq5047
  have eq5082 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5046 eq1483
    | exact resolve eq1483 eq5046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1483
  have eq5097 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq5082
       have r₂ := eq27
       grind)
    | exact resolve eq5082 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5082
  have eq5233 : x = (M.op (M.op x x) y) := by
    first
    | exact superpose eq5050 eq235
    | exact resolve eq235 eq5050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq5469 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5097 eq170
    | exact resolve eq170 eq5097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170 eq5097
  have eq5496 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5050 eq5469
    | exact resolve eq5469 eq5050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5469
  have eq5689 : ∀ X0 : G, x = (M.op (M.op (τ (M.op (σ x) (σ y))) (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq14 x x X0
       have i₂ := eq5496
       grind)
    | exact superpose eq5496 eq14
    | exact resolve eq14 eq5496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5690 : ∀ X0 : G, x = (M.op (M.op (M.op x X0) (τ (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 x
       have i₂ := eq5496
       grind)
    | exact superpose eq5496 eq14
    | exact resolve eq14 eq5496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5730 : x = (M.op (τ (M.op (σ x) (σ y))) y) := by
    first
    | (have i₁ := eq5233
       have i₂ := eq5496
       grind)
    | exact superpose eq5496 eq5233
    | exact resolve eq5233 eq5496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5233
  have eq5747 : ∀ X1 : G, x = (M.op (M.op (M.op x x) (M.op x y)) (M.op (M.op (M.op x x) (M.op x y)) X1)) := by
    intro X1
    first
    | (have i₁ := eq653 x X1
       have i₂ := eq651 x sF0 x
       grind)
    | exact superpose eq651 eq653
    | exact resolve eq653 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq5748 : ∀ X1 : G, x = (M.op (M.op (M.op x x) x) (M.op (M.op (M.op x x) x) X1)) := by
    intro X1
    first
    | exact superpose eq5050 eq5747
    | exact resolve eq5747 eq5050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5747
  have eq5749 : ∀ X1 : G, x = (M.op (M.op (τ (M.op (σ x) (σ y))) x) (M.op (M.op (τ (M.op (σ x) (σ y))) x) X1)) := by
    intro X1
    first
    | (have i₁ := eq5748 X1
       have i₂ := eq5496
       grind)
    | exact superpose eq5496 eq5748
    | exact resolve eq5748 eq5496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5748
  have eq5752 : x = (M.op (M.op (τ (M.op (σ x) (σ y))) x) x) := by
    first
    | exact superpose eq5749 eq5749
    | exact resolve eq5749 eq5749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5749
  have eq5780 : ∀ X0 : G, (M.op x (M.op (M.op (τ (M.op (σ x) (σ y))) x) X0)) = (M.op (M.op (M.op (τ (M.op (σ x) (σ y))) x) (M.op (τ (M.op (σ x) (σ y))) x)) x) := by
    intro X0
    first
    | exact superpose eq5752 eq651
    | exact resolve eq651 eq5752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5752
  have eq5783 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op x (M.op (M.op (τ (M.op (σ x) (σ y))) x) X0)) := by
    intro X0
    first
    | (have i₁ := eq5780 X0
       have i₂ := eq14 (τ sF4) x x
       grind)
    | exact superpose eq14 eq5780
    | exact resolve eq5780 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5780
  have eq6833 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X1)) (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X3)) = X0 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq652 X0 X1 x X3
       have i₂ := eq651 X0 (M.op X0 X1) x
       grind)
    | exact superpose eq651 eq652
    | exact resolve eq652 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq6834 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op X0 X0) X0) X3)) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq6833 x x X3
       have i₂ := eq651 x x x
       grind)
    | exact superpose eq651 eq6833
    | exact resolve eq6833 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6833
  have eq8698 : x = (M.op (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) x) := by
    first
    | (have i₁ := eq5689 x
       have i₂ := eq5496
       grind)
    | exact superpose eq5496 eq5689
    | exact resolve eq5689 eq5496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5496 eq5689
  have eq8818 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op (M.op x X0) x) X1)) = (M.op (M.op (M.op (M.op x X0) x) (M.op (M.op x (M.op (M.op (M.op x X0) x) X1)) X2)) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq5050 eq633
    | exact resolve eq633 eq5050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq8924 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op (τ (M.op (σ x) (σ y))) x) X1)) = (M.op (M.op (M.op (τ (M.op (σ x) (σ y))) x) (M.op (M.op x (M.op (M.op (τ (M.op (σ x) (σ y))) x) X1)) X2)) (M.op (M.op (τ (M.op (σ x) (σ y))) x) X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq5783 eq8818
    | exact resolve eq8818 eq5783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8818
  have eq8937 : ∀ X1 X2 : G, (M.op x (M.op (M.op (τ (M.op (σ x) (σ y))) x) X1)) = (M.op (M.op (M.op (τ (M.op (σ x) (σ y))) x) (M.op (τ (M.op (σ x) (σ y))) x)) (M.op (M.op x (M.op (M.op (τ (M.op (σ x) (σ y))) x) X1)) X2)) := by
    intro X1 X2
    first
    | (have i₁ := eq8924 X2 X1 X2
       have i₂ := eq651 (M.op (τ sF4) x) (M.op (M.op x (M.op (M.op (τ sF4) x) X1)) X2) X2
       grind)
    | exact superpose eq651 eq8924
    | exact resolve eq8924 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8924
  have eq8947 : ∀ X2 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op (M.op (τ (M.op (σ x) (σ y))) x) (M.op (τ (M.op (σ x) (σ y))) x)) (M.op (τ (M.op (σ x) (σ y))) X2)) := by
    intro X2
    first
    | exact superpose eq5783 eq8937
    | exact resolve eq8937 eq5783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8937
  have eq8950 : ∀ X2 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) x) (M.op (τ (M.op (σ x) (σ y))) X2)) := by
    intro X2
    first
    | (have i₁ := eq8947 X2
       have i₂ := eq651 (τ sF4) x x
       grind)
    | exact superpose eq651 eq8947
    | exact resolve eq8947 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8947
  have eq8951 : ∀ X2 : G, (τ (M.op (σ x) (σ y))) = (M.op x (M.op (τ (M.op (σ x) (σ y))) X2)) := by
    intro X2
    first
    | exact superpose eq8698 eq8950
    | exact resolve eq8950 eq8698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8698 eq8950
  have eq8973 : ∀ X0 : G, x = (M.op (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) (M.op (τ (M.op (σ x) (σ y))) X0)) := by
    intro X0
    first
    | exact superpose eq8951 eq5690
    | exact resolve eq5690 eq8951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5690
  have eq8990 : x = (M.op (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq8973 x
       have i₂ := eq651 (τ sF4) (τ sF4) x
       grind)
    | exact superpose eq651 eq8973
    | exact resolve eq8973 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651 eq8973
  have eq9008 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq8990 eq6834
    | exact resolve eq6834 eq8990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6834 eq8990
  have eq9028 : (τ (M.op (σ x) (σ y))) = (M.op x (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq5783 eq9008
    | exact resolve eq9008 eq5783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5783 eq9008
  have eq9105 : ∀ X0 : G, (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) = (M.op (M.op x (M.op (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) X0)) y) := by
    intro X0
    first
    | exact superpose eq9028 eq238
    | exact resolve eq238 eq9028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq9140 : ∀ X0 : G, (M.op x (τ (M.op (σ x) (σ y)))) = (M.op (M.op x (M.op (M.op x (τ (M.op (σ x) (σ y)))) X0)) y) := by
    intro X0
    first
    | exact superpose eq5050 eq9105
    | exact resolve eq9105 eq5050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5050 eq9105
  have eq9148 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op x (M.op (τ (M.op (σ x) (σ y))) X0)) y) := by
    intro X0
    first
    | exact superpose eq9028 eq9140
    | exact resolve eq9140 eq9028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9028 eq9140
  have eq9152 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) y) := by
    first
    | exact superpose eq8951 eq9148
    | exact resolve eq9148 eq8951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8951 eq9148
  have eq9154 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5730 eq9152
    | exact resolve eq9152 eq5730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5730 eq9152
  have eq9178 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9154 eq15
    | exact resolve eq15 eq9154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9154
  have eq9223 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9178
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9178
    | exact resolve eq9178 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq9178
  have eq9250 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5046 eq9223
    | exact resolve eq9223 eq5046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5046 eq9223
  have eq9272 : False := by grind
  exact eq9272
