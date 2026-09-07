import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4279`: `x ◇ (x ◇ x) = y ◇ (z ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then Y else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_y_y_pyx_Equation4279 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4279 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4279.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X2 X1)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq20 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X4 X3)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq9 x X3 X4
       have i₂ := eq9 x X0 X1
       grind)
    | (have i₁ := eq9 x X1 x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ X2 ∨ (k (M.op X2 X2) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X2 X2) X2
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq12 (M.op X2 X1) X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X2 X2) X2
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 (M.op X2 X1)) (M.op X1 (M.op X2 X1))) (M.op X1 (M.op X2 X1))
       have r₂ := eq9 (M.op X1 (M.op X2 X1)) X1 X2
       grind)
    | (have r₁ := eq12 (M.op X2 (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))
       have r₂ := eq9 X0 (M.op X0 (M.op X0 X0)) X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq49 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op X3 X2)) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 X3
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq52 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq51 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq51 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq75 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op X4 X5) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq20 X2 X3 (M.op X4 X5) X5
       have i₂ := eq20 X5 X4 X0 X1
       grind)
    | (have i₁ := eq20 X2 X3 (M.op X4 X5) X5
       have i₂ := eq20 X0 X1 X5 X4
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq52
    | exact resolve eq52 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq52 (τ X1) X0
       grind)
    | exact superpose eq52 eq18
    | (have j1 := eq52 (τ X1) X0
       grind)
    | exact resolve eq18 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq137 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq26 X0 X1 (M.op X0 (M.op X1 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq380 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq50 (σ y) (σ x) X0 X1
       grind)
    | exact superpose eq50 eq16
    | (have j1 := eq50 (σ y) (σ x) x x
       grind)
    | exact resolve eq16 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq418 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq380 X0 X1
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq380
    | (have j0 := eq380 X0 X1
       grind)
    | exact resolve eq380 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq459 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X0
       have i₂ := eq14 X0 (σ X0)
       grind)
    | (have i₁ := eq45 X0 X1
       have i₂ := eq14 (M.op (σ X0) (σ X1)) X1
       grind)
    | exact superpose eq14 eq45
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq45 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : ∀ X0 : G, (σ X0) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq524 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq45 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq525 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq526 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq524 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq533 : ∀ X0 : G, (σ X0) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq486 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq537 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq459 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq545 : ∀ X0 : G, (σ X0) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq533 X0
       have j1 := eq12 (σ (k X0 X0)) (σ X0)
       grind)
    | (have r₁ := eq533 X0
       have r₂ := eq12 (σ (k X0 X0)) (σ X0)
       grind)
    | (have r₁ := eq533 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | exact resolve eq533 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq555 : ∀ X0 : G, (σ X0) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq545 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq545
    | (have j0 := eq545 X0
       grind)
    | exact resolve eq545 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq1101 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq109 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq109
    | exact resolve eq109 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq1132 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1101 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1101
    | (have j0 := eq1101 X0 X1
       grind)
    | exact resolve eq1101 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101
  have eq1192 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq103 y x
       grind)
    | exact superpose eq103 eq16
    | (have j1 := eq103 y x
       grind)
    | exact resolve eq16 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1207 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 X2 X3 (σ X0) (σ X1)
       have i₂ := eq103 X0 X1
       grind)
    | exact superpose eq103 eq20
    | (have j1 := eq103 X0 X1
       grind)
    | exact resolve eq20 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq6744 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq1192
       have i₂ := eq1132 y x
       grind)
    | exact superpose eq1132 eq1192
    | (have j1 := eq1132 y x
       grind)
    | (have r₁ := eq1192
       have r₂ := eq1132 y x
       grind)
    | exact resolve eq1192 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132 eq1192
  have eq6745 : (σ (M.op x y)) = (σ x) ∨ x = (k y x) := by grind
  clear eq6744
  have eq6924 : (M.op x y) = (τ (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq6745
       grind)
    | exact superpose eq6745 eq10
    | exact resolve eq10 eq6745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6745
  have eq6963 : x = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq6924
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6924
    | exact resolve eq6924 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6924
  have eq6964 : x = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq6963
       have r₂ := eq12 y x
       grind)
    | exact resolve eq6963 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6963
  have eq7259 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq6964
       grind)
    | exact superpose eq6964 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq6964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7264 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq7259
  have eq7544 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1 y x
       have i₂ := eq7264
       grind)
    | exact superpose eq7264 eq20
    | exact resolve eq20 eq7264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8284 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (k (M.op X0 (M.op X1 X0)) (M.op X2 (M.op X3 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq137 X2 X3
       have i₂ := eq75 X2 X3 X0 X1 X2 (M.op X3 X2)
       grind)
    | exact superpose eq75 eq137
    | exact resolve eq137 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq137
  have eq9716 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq525 x y
       have i₂ := eq6964
       grind)
    | exact superpose eq6964 eq525
    | (have j0 := eq525 x y
       grind)
    | exact resolve eq525 eq6964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9733 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq9716
  have eq10262 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9733
       grind)
    | exact superpose eq9733 eq16
    | exact resolve eq16 eq9733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9733
  have eq10369 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10262
       have i₂ := eq7264
       grind)
    | exact superpose eq7264 eq10262
    | exact resolve eq10262 eq7264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10262
  have eq10372 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq10369
  have eq10723 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq45 x x
       have i₂ := eq10372
       grind)
    | exact superpose eq10372 eq45
    | exact resolve eq45 eq10372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq10774 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 (σ x) (σ x)
       have i₂ := eq10372
       grind)
    | exact superpose eq10372 eq12
    | (have j0 := eq12 (σ x) (σ x)
       grind)
    | exact resolve eq12 eq10372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10822 : (M.op (σ x) (σ y)) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq7544 (σ x) (σ x)
       have i₂ := eq10372
       grind)
    | exact superpose eq10372 eq7544
    | exact resolve eq7544 eq10372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10372
  have eq10823 : (M.op (σ x) (σ y)) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq10822
  have eq10824 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq10723
  have eq10829 : (σ x) = (σ (k x x)) ∨ (σ x) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10774
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq10774
    | exact resolve eq10774 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10774
  have eq11556 : (σ (M.op x y)) ≠ (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10823
       grind)
    | exact superpose eq10823 eq16
    | exact resolve eq16 eq10823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10823
  have eq12259 : (σ x) ≠ (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11556
       have i₂ := eq7264
       grind)
    | exact superpose eq7264 eq11556
    | exact resolve eq11556 eq7264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7264 eq11556
  have eq12261 : (σ x) ≠ (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq12259
  have eq21760 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq537 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq537
    | (have j0 := eq537 X1 (τ X0)
       grind)
    | exact resolve eq537 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq21957 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21760 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq21760
    | (have j0 := eq21760 X0 X1
       grind)
    | exact resolve eq21760 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq21760
  have eq21967 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X0 X0) = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21957 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21957
    | (have j0 := eq21957 X0 X1
       grind)
    | exact resolve eq21957 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21957
  have eq33523 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq10824
       grind)
    | exact superpose eq10824 eq10
    | exact resolve eq10 eq10824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10824
  have eq33576 : y = (k x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq33523
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq33523
    | exact resolve eq33523 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33523
  have eq34609 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq33576
       have i₂ := eq52 x x
       grind)
    | exact superpose eq52 eq33576
    | (have j1 := eq52 x x
       grind)
    | exact resolve eq33576 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq33576
  have eq34656 : x = (k x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq34609
  have eq37252 : (σ x) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq555 x
       have i₂ := eq34656
       grind)
    | exact superpose eq34656 eq555
    | (have j0 := eq555 x
       grind)
    | exact resolve eq555 eq34656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555 eq34656
  have eq37288 : (σ x) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq37252
       have r₂ := eq10829
       grind)
    | exact resolve eq37252 eq10829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10829 eq37252
  have eq37290 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq526 x
       grind)
    | (have r₁ := eq37288
       have r₂ := eq526 x
       grind)
    | exact resolve eq37288 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526 eq37288
  have eq40406 : (M.op (σ x) (σ x)) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq7544 (σ x) (σ x)
       have i₂ := eq37290
       grind)
    | exact superpose eq37290 eq7544
    | exact resolve eq7544 eq37290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7544
  have eq40415 : (M.op (σ x) (σ x)) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq40406
  have eq49288 : (σ x) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq37290
       have i₂ := eq40415
       grind)
    | exact superpose eq40415 eq37290
    | exact resolve eq37290 eq40415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37290 eq40415
  have eq49482 : (σ x) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq49288
  have eq49497 : y = (M.op x x) := by
    first
    | (have r₁ := eq49482
       have r₂ := eq12261
       grind)
    | exact resolve eq49482 eq12261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12261 eq49482
  have eq50718 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1 x x
       have i₂ := eq49497
       grind)
    | exact superpose eq49497 eq20
    | exact resolve eq20 eq49497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53458 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq50718 (M.op X0 X1) X1
       have i₂ := eq50718 X1 X0
       grind)
    | exact superpose eq50718 eq50718
    | exact resolve eq50718 eq50718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53871 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op x y)) = (k (M.op X2 (M.op X3 X2)) (M.op (M.op X0 X1) (M.op x y))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8284 X0 X1 (M.op X1 X0) X0
       have i₂ := eq50718 X0 X1
       grind)
    | exact superpose eq50718 eq8284
    | exact resolve eq8284 eq50718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8284
  have eq53933 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op x y)) = (k (M.op x y) (M.op (M.op X0 X1) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq53871 X0 X1 x x
       have i₂ := eq50718 x x
       grind)
    | exact superpose eq50718 eq53871
    | exact resolve eq53871 eq50718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53871
  have eq54121 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq53933 x x
       have i₂ := eq53458 x x
       grind)
    | exact superpose eq53458 eq53933
    | exact resolve eq53933 eq53458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53458 eq53933
  have eq58915 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq525 (M.op x y) (M.op x y)
       have i₂ := eq54121
       grind)
    | exact superpose eq54121 eq525
    | (have j0 := eq525 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq525 eq54121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525 eq54121
  have eq58921 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq58915
  have eq58922 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq58921
  have eq95263 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1 (σ (M.op x y)) (σ (M.op x y))
       have i₂ := eq58922
       grind)
    | exact superpose eq58922 eq20
    | exact resolve eq20 eq58922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq95340 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq418 (σ (M.op x y)) (σ (M.op x y))
       have i₂ := eq58922
       grind)
    | exact superpose eq58922 eq418
    | exact resolve eq418 eq58922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq95430 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq95340
       have r₂ := eq58922
       grind)
    | exact resolve eq95340 eq58922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95340
  have eq95494 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq95263 X0 X1
       have i₂ := eq58922
       grind)
    | exact superpose eq58922 eq95263
    | exact resolve eq95263 eq58922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58922 eq95263
  have eq95633 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq95430
       have i₂ := eq6964
       grind)
    | exact superpose eq6964 eq95430
    | exact resolve eq95430 eq6964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95430
  have eq95634 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq95633
  have eq95677 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq95494 x x
       have i₂ := eq50718 x x
       grind)
    | exact superpose eq50718 eq95494
    | exact resolve eq95494 eq50718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95494
  have eq97283 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq95634
       grind)
    | exact superpose eq95634 eq16
    | exact resolve eq16 eq95634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97514 : (M.op x y) ≠ (σ x) := by
    first
    | (have i₁ := eq97283
       have i₂ := eq95677
       grind)
    | exact superpose eq95677 eq97283
    | exact resolve eq97283 eq95677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97283
  have eq116418 : x = (M.op x y) ∨ y = (k x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6964
       have i₂ := eq21967 x y
       grind)
    | exact superpose eq21967 eq6964
    | (have j1 := eq21967 x y
       grind)
    | exact resolve eq6964 eq21967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6964 eq21967
  have eq116601 : y = (k x x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq116418
  have eq116846 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X1 X0)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq1207 x x x x
       have i₂ := eq116601
       grind)
    | exact superpose eq116601 eq1207
    | exact resolve eq1207 eq116601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207 eq116601
  have eq116872 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq116846 x x
       have i₂ := eq50718 x x
       grind)
    | exact superpose eq50718 eq116846
    | exact resolve eq116846 eq50718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50718 eq116846
  have eq116885 : (M.op x y) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq116872
       have i₂ := eq95634
       grind)
    | exact superpose eq95634 eq116872
    | exact resolve eq116872 eq95634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95634 eq116872
  have eq116892 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq116885
       have r₂ := eq97514
       grind)
    | exact resolve eq116885 eq97514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116885
  have eq129539 : x = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq95677
       have i₂ := eq116892
       grind)
    | exact superpose eq116892 eq95677
    | exact resolve eq95677 eq116892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129542 : x ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq97514
       have i₂ := eq116892
       grind)
    | exact superpose eq116892 eq97514
    | exact resolve eq97514 eq116892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116892
  have eq129748 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq129539
       have r₂ := eq129542
       grind)
    | exact resolve eq129539 eq129542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129539 eq129542
  have eq130114 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq129748
       grind)
    | exact superpose eq129748 eq10
    | exact resolve eq10 eq129748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129748
  have eq130255 : x = y ∨ x = y := by
    first
    | (have i₁ := eq130114
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq130114
    | exact resolve eq130114 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130114
  have eq130256 : x = y := by grind
  clear eq130255
  have eq130688 : (M.op x x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq95677
       have i₂ := eq130256
       grind)
    | exact superpose eq130256 eq95677
    | exact resolve eq95677 eq130256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95677
  have eq130692 : (σ x) ≠ (M.op x x) := by
    first
    | (have i₁ := eq97514
       have i₂ := eq130256
       grind)
    | exact superpose eq130256 eq97514
    | exact resolve eq97514 eq130256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97514
  have eq130711 : y ≠ (σ x) := by
    first
    | (have i₁ := eq130692
       have i₂ := eq49497
       grind)
    | exact superpose eq49497 eq130692
    | exact resolve eq130692 eq49497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130692
  have eq130715 : y = (σ y) := by
    first
    | (have i₁ := eq130688
       have i₂ := eq49497
       grind)
    | exact superpose eq49497 eq130688
    | exact resolve eq130688 eq49497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49497 eq130688
  have eq130747 : x ≠ (σ x) := by
    first
    | (have i₁ := eq130711
       have i₂ := eq130256
       grind)
    | exact superpose eq130256 eq130711
    | exact resolve eq130711 eq130256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130711
  have eq130751 : x = (σ x) := by
    first
    | (have i₁ := eq130715
       have i₂ := eq130256
       grind)
    | exact superpose eq130256 eq130715
    | exact resolve eq130715 eq130256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130256 eq130715
  have eq130776 : False := by grind
  exact eq130776

/-- `Equation4279`: `x ◇ (x ◇ x) = y ◇ (z ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyx_y_pxx_pyx_Equation4279 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4279 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4279.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X2 X1)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq20 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X4 X3)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq9 x X3 X4
       have i₂ := eq9 x X0 X1
       grind)
    | (have i₁ := eq9 x X1 x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
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
  have eq40 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq32 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32
    | exact resolve eq32 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq62 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq65 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29
    | exact resolve eq29 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  clear eq29
  have eq75 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq68
    | exact resolve eq68 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq120 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq30 (σ X0)
       grind)
    | exact superpose eq30 eq15
    | (have j1 := eq30 (σ X0)
       grind)
    | exact resolve eq15 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq492 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq498 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq492 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq492 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq492 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq492 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq492 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq527 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq544 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X1
       have i₂ := eq498 X0 (σ X1)
       grind)
    | (have i₁ := eq75 X0
       have i₂ := eq498 (M.op (σ X0) (σ X0)) X1
       grind)
    | exact superpose eq498 eq75
    | (have j1 := eq498 X0 (σ X1)
       grind)
    | exact resolve eq75 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq551 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq498 (σ X1) (σ X0)
       grind)
    | exact superpose eq498 eq15
    | (have j1 := eq498 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0
       have i₂ := eq498 (σ X1) X0
       grind)
    | exact superpose eq498 eq37
    | (have j1 := eq498 (σ X1) X0
       grind)
    | exact resolve eq37 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq555 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq498 (τ X1) X0
       grind)
    | exact superpose eq498 eq18
    | (have j1 := eq498 (τ X1) X0
       grind)
    | exact resolve eq18 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq665 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq527 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4225 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq120 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq6300 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4225 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq4225
    | (have j0 := eq4225 (τ X0)
       grind)
    | exact resolve eq4225 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6307 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6300 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6300
    | (have j0 := eq6300 X0
       grind)
    | exact resolve eq6300 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6300
  have eq6311 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6307 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6307
    | (have j0 := eq6307 X0
       grind)
    | exact resolve eq6307 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6307
  have eq6680 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq6311 (τ X0)
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq6311
    | (have j0 := eq6311 (τ X0)
       grind)
    | exact resolve eq6311 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6311
  have eq9092 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq544 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq544
    | (have j0 := eq544 (σ X0) X1
       grind)
    | exact resolve eq544 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9122 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X0)) ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 X1
       have i₂ := eq544 X1 (τ X0)
       grind)
    | exact superpose eq544 eq65
    | (have j1 := eq544 X1 (τ X0)
       grind)
    | exact resolve eq65 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq544
  have eq9181 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9122 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9122
    | (have j0 := eq9122 X0 X1
       grind)
    | exact resolve eq9122 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9122
  have eq9189 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9092 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9092
    | (have j0 := eq9092 X0 X1
       grind)
    | exact resolve eq9092 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9092
  have eq9795 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (τ X0) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0
       have i₂ := eq9181 X0 (σ X1)
       grind)
    | exact superpose eq9181 eq37
    | (have j1 := eq9181 X0 (σ X1)
       grind)
    | exact resolve eq37 eq9181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq9181
  have eq17116 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9189 y x
       grind)
    | exact superpose eq9189 eq16
    | (have j1 := eq9189 y x
       grind)
    | exact resolve eq16 eq9189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17592 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq17116
       have i₂ := eq498 y x
       grind)
    | exact superpose eq498 eq17116
    | (have j1 := eq498 y x
       grind)
    | exact resolve eq17116 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq17593 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq17116
       have i₂ := eq527 y x
       grind)
    | exact superpose eq527 eq17116
    | (have j1 := eq527 y x
       grind)
    | exact resolve eq17116 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17116
  have eq17597 : x = (M.op x y) ∨ x = (k y x) := by grind
  clear eq17593
  have eq17598 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq17592
  have eq17608 : x = (k y x) := by
    first
    | (have j1 := eq665 y x
       grind)
    | (have r₁ := eq17597
       have r₂ := eq665 y x
       grind)
    | exact resolve eq17597 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17597
  have eq18634 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1 y x
       have i₂ := eq17598
       grind)
    | exact superpose eq17598 eq20
    | exact resolve eq20 eq17598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24490 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq552 X0 X1
       grind)
    | exact superpose eq552 eq10
    | (have j1 := eq552 X0 X1
       grind)
    | exact resolve eq10 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq32481 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq555 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq555
    | exact resolve eq555 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq32845 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq32481 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq32481
    | (have j0 := eq32481 X0 X1
       grind)
    | exact resolve eq32481 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32481
  have eq33925 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq32845 y x
       have i₂ := eq17608
       grind)
    | exact superpose eq17608 eq32845
    | (have j0 := eq32845 y x
       grind)
    | exact resolve eq32845 eq17608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34256 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (σ (k X0 (τ X1))) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X1
       have i₂ := eq32845 X0 (τ X1)
       grind)
    | (have i₁ := eq40 X0
       have i₂ := eq32845 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact superpose eq32845 eq40
    | (have j1 := eq32845 X0 (τ X1)
       grind)
    | exact resolve eq40 eq32845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq32845
  have eq34287 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34256 X0 X1
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq34256
    | (have j0 := eq34256 X0 X1
       grind)
    | exact resolve eq34256 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq34256
  have eq83729 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34287 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq34287
    | (have j0 := eq34287 X1 (σ X0)
       grind)
    | exact resolve eq34287 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34287
  have eq84089 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq83729 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq83729
    | (have j0 := eq83729 X0 X1
       grind)
    | exact resolve eq83729 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83729
  have eq84128 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq84089 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq84089
    | (have j0 := eq84089 X0 X1
       grind)
    | exact resolve eq84089 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84089
  have eq96430 : ∀ X0 : G, (τ (σ X0)) ≠ (τ (M.op (σ X0) (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (τ (σ X0)) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq6680 (σ X0)
       have i₂ := eq9795 (σ X0) X0
       grind)
    | exact superpose eq9795 eq6680
    | (have j0 := eq6680 (σ X0)
       have j1 := eq9795 (σ X0) X0
       grind)
    | exact resolve eq6680 eq9795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6680 eq9795
  have eq96468 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (τ (σ X0)) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq96430 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq96430
    | (have j0 := eq96430 X0
       grind)
    | exact resolve eq96430 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96430
  have eq96488 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (τ (σ X0)) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq96468 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq96468
    | (have j0 := eq96468 X0
       grind)
    | exact resolve eq96468 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96468
  have eq96490 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq96488 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq96488
    | (have j0 := eq96488 X0
       grind)
    | exact resolve eq96488 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96488
  have eq96492 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq96490 X0
       have j1 := eq665 X0 X0
       grind)
    | (have r₁ := eq96490 X0
       have r₂ := eq665 X0 X0
       grind)
    | exact resolve eq96490 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665 eq96490
  have eq117808 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4225 X0
       have i₂ := eq84128 X0 X0
       grind)
    | exact superpose eq84128 eq4225
    | (have j0 := eq4225 X0
       have j1 := eq84128 X0 X0
       grind)
    | (have r₁ := eq4225 x
       have r₂ := eq84128 x x
       grind)
    | exact resolve eq4225 eq84128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84128
  have eq117905 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq117808 X0
       have j1 := eq4225 X0
       grind)
    | (have r₁ := eq117808 X0
       have r₂ := eq4225 X0
       grind)
    | exact resolve eq117808 eq4225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117808
  have eq268332 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq551 x y
       grind)
    | exact superpose eq551 eq16
    | (have j1 := eq551 x y
       grind)
    | exact resolve eq16 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq268480 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq268332
       have i₂ := eq17608
       grind)
    | exact superpose eq17608 eq268332
    | exact resolve eq268332 eq17608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17608 eq268332
  have eq268504 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq268480
       have i₂ := eq33925
       grind)
    | exact superpose eq33925 eq268480
    | (have r₁ := eq268480
       have r₂ := eq33925
       grind)
    | exact resolve eq268480 eq33925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268480
  have eq268506 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq268504
  have eq268691 : x ≠ (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq96492 x
       have i₂ := eq268506
       grind)
    | exact superpose eq268506 eq96492
    | (have j0 := eq96492 x
       grind)
    | exact resolve eq96492 eq268506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96492
  have eq268700 : (τ (σ y)) = (k x (τ (σ x))) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq24490 (σ x) x
       have i₂ := eq268506
       grind)
    | exact superpose eq268506 eq24490
    | exact resolve eq24490 eq268506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24490
  have eq268791 : (M.op (σ x) (σ y)) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18634 (σ x) (σ x)
       have i₂ := eq268506
       grind)
    | exact superpose eq268506 eq18634
    | exact resolve eq18634 eq268506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268506
  have eq268797 : (M.op (σ x) (σ y)) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq268791
  have eq268819 : (k x x) = (τ (σ y)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq268700
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq268700
    | exact resolve eq268700 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268700
  have eq268825 : x ≠ y ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq268691
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq268691
    | exact resolve eq268691 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268691
  have eq268840 : y = (k x x) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq268819
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq268819
    | exact resolve eq268819 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268819
  have eq268850 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq268840
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq268840
    | exact resolve eq268840 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268840
  have eq270317 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq527 x x
       have i₂ := eq268850
       grind)
    | exact superpose eq268850 eq527
    | exact resolve eq527 eq268850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527 eq268850
  have eq270333 : y = (M.op x x) ∨ x = y := by grind
  clear eq270317
  have eq270955 : y ≠ y ∨ x = y ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq270333
       grind)
    | exact superpose eq270333 eq13
    | exact resolve eq13 eq270333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270957 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 X0)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1 x x
       have i₂ := eq270333
       grind)
    | exact superpose eq270333 eq20
    | exact resolve eq20 eq270333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270333
  have eq271014 : y ≠ y ∨ x = y ∨ y = (k x x) := by grind
  clear eq270955
  have eq271015 : y = (k x x) ∨ x = y := by grind
  clear eq271014
  have eq273050 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) (M.op x y)) ∨ x = y ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq270957 (M.op X0 X1) X1
       have i₂ := eq270957 X1 X0
       grind)
    | exact superpose eq270957 eq270957
    | exact resolve eq270957 eq270957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270957
  have eq273367 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) (M.op x y)) ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq273050 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273050
  have eq274033 : (σ (M.op x y)) ≠ (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq268797
       grind)
    | exact superpose eq268797 eq16
    | exact resolve eq16 eq268797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268797
  have eq274182 : (σ x) ≠ (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq274033
       have i₂ := eq33925
       grind)
    | exact superpose eq33925 eq274033
    | exact resolve eq274033 eq33925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33925 eq274033
  have eq274184 : (σ x) ≠ (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq274182
  have eq274713 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y := by grind
  clear eq273367
  have eq276964 : x = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq274713
       have i₂ := eq17598
       grind)
    | exact superpose eq17598 eq274713
    | exact resolve eq274713 eq17598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17598 eq274713
  have eq276998 : x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq276964
       have r₂ := eq268825
       grind)
    | exact resolve eq276964 eq268825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268825 eq276964
  have eq277052 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4225 x
       have i₂ := eq276998
       grind)
    | exact superpose eq276998 eq4225
    | (have j0 := eq4225 x
       grind)
    | exact resolve eq4225 eq276998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4225 eq276998
  have eq277095 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq277052
  have eq279662 : (M.op (σ x) (σ x)) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18634 (σ x) (σ x)
       have i₂ := eq277095
       grind)
    | exact superpose eq277095 eq18634
    | exact resolve eq18634 eq277095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18634
  have eq279674 : (M.op (σ x) (σ x)) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq279662
  have eq283474 : (σ x) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq277095
       have i₂ := eq279674
       grind)
    | exact superpose eq279674 eq277095
    | exact resolve eq277095 eq279674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277095 eq279674
  have eq283609 : (σ x) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq283474
  have eq283633 : y = (M.op x x) := by
    first
    | (have r₁ := eq283609
       have r₂ := eq274184
       grind)
    | exact resolve eq283609 eq274184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274184 eq283609
  have eq283744 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq117905 x
       have i₂ := eq283633
       grind)
    | exact superpose eq283633 eq117905
    | (have j0 := eq117905 x
       grind)
    | exact resolve eq117905 eq283633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283748 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1 x x
       have i₂ := eq283633
       grind)
    | exact superpose eq283633 eq20
    | exact resolve eq20 eq283633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283962 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq283748 (M.op X0 X1) X1
       have i₂ := eq283748 X1 X0
       grind)
    | exact superpose eq283748 eq283748
    | exact resolve eq283748 eq283748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq284016 : ∀ X0 X1 : G, (M.op x y) = (M.op (σ X0) (σ (k X0 X1))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq283748 (σ X0) (σ X1)
       have i₂ := eq9189 X0 X1
       grind)
    | exact superpose eq9189 eq283748
    | (have j1 := eq9189 X0 X1
       grind)
    | exact resolve eq283748 eq9189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9189
  have eq285413 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq117905 (M.op x y)
       have i₂ := eq283962 x y
       grind)
    | exact superpose eq283962 eq117905
    | (have j0 := eq117905 (M.op x y)
       grind)
    | exact resolve eq117905 eq283962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117905 eq283962
  have eq285521 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq285413
  have eq296379 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1 (σ (M.op x y)) (σ (M.op x y))
       have i₂ := eq285521
       grind)
    | exact superpose eq285521 eq20
    | exact resolve eq20 eq285521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq296559 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq296379 X0 X1
       have i₂ := eq285521
       grind)
    | exact superpose eq285521 eq296379
    | exact resolve eq296379 eq285521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285521 eq296379
  have eq296694 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq296559 x x
       have i₂ := eq283748 x x
       grind)
    | exact superpose eq283748 eq296559
    | exact resolve eq296559 eq283748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283748 eq296559
  have eq356177 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq284016 x x
       have i₂ := eq271015
       grind)
    | exact superpose eq271015 eq284016
    | exact resolve eq284016 eq271015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271015 eq284016
  have eq356292 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq356177
  have eq356375 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq356292
       grind)
    | exact superpose eq356292 eq16
    | exact resolve eq16 eq356292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356292
  have eq356561 : x = y := by
    first
    | (have r₁ := eq356375
       have r₂ := eq296694
       grind)
    | exact resolve eq356375 eq296694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296694 eq356375
  have eq356843 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq356561
       grind)
    | exact superpose eq356561 eq16
    | exact resolve eq16 eq356561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356900 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq283744
       have i₂ := eq356561
       grind)
    | exact superpose eq356561 eq283744
    | exact resolve eq283744 eq356561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283744
  have eq356955 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq356900
  have eq357038 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq356843
       have i₂ := eq283633
       grind)
    | exact superpose eq283633 eq356843
    | exact resolve eq356843 eq283633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283633 eq356843
  have eq357077 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq357038
       have i₂ := eq356955
       grind)
    | exact superpose eq356955 eq357038
    | exact resolve eq357038 eq356955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356955 eq357038
  have eq357093 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq357077
       have i₂ := eq356561
       grind)
    | exact superpose eq356561 eq357077
    | exact resolve eq357077 eq356561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356561 eq357077
  have eq357094 : False := by grind
  exact eq357094

/-- `Equation4293`: `x ◇ (x ◇ y) = y ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(Y,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_pyy_pyy_pxx_pyx_Equation4293 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4293 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4293.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq31 (σ X0)
       grind)
    | exact superpose eq31 eq15
    | exact resolve eq15 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq31 (τ X0)
       grind)
    | exact superpose eq31 eq18
    | exact resolve eq18 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq35
    | exact resolve eq35 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq38 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq33
    | exact resolve eq33 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq40 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq36
    | exact resolve eq36 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq36
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq68 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
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
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq76 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq86 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X1
       have i₂ := eq38 X1
       grind)
    | exact superpose eq38 eq75
    | (have j0 := eq75 X0 X1
       grind)
    | exact resolve eq75 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq88 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       have j1 := eq80 X0 X1
       grind)
    | (have r₁ := eq82 X0 X1
       have r₂ := eq80 X0 X1
       grind)
    | (have r₁ := eq82 X1 X0
       have r₂ := eq80 X0 X1
       grind)
    | (have r₁ := eq82 X1 X1
       have r₂ := eq80 X1 X1
       grind)
    | exact resolve eq82 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq82
  have eq91 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq127 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0
       have i₂ := eq14 X1 (τ X0)
       grind)
    | (have i₁ := eq40 X0
       have i₂ := eq14 (τ X0) (τ X0)
       grind)
    | exact superpose eq14 eq40
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq40 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq10
    | exact resolve eq10 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq88
    | (have j0 := eq88 (σ X1) (σ X0)
       grind)
    | exact resolve eq88 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq88 X1 (τ X0)
       grind)
    | exact superpose eq88 eq17
    | (have j1 := eq88 X1 (τ X0)
       grind)
    | exact resolve eq17 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq280 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq88 (τ X0) X1
       grind)
    | exact superpose eq88 eq18
    | (have j1 := eq88 (τ X0) X1
       grind)
    | exact resolve eq18 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq295 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq268 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq268
    | (have j0 := eq268 X0 X1
       grind)
    | exact resolve eq268 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq303 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq251 X0 X1
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq251
    | (have j0 := eq251 X0 X1
       grind)
    | exact resolve eq251 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq312 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ X0)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq295 X0 X1
       have i₂ := eq147 X0
       grind)
    | exact superpose eq147 eq295
    | (have j0 := eq295 X0 X1
       grind)
    | exact resolve eq295 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq317 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq303 X0 X1
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq303
    | (have j0 := eq303 X0 X1
       grind)
    | exact resolve eq303 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq334 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq147 X0
       grind)
    | exact superpose eq147 eq12
    | (have j0 := eq12 (τ X0) X1
       grind)
    | exact resolve eq12 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq922 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq91 X1 X0
       grind)
    | exact superpose eq91 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq91 X1 X0
       grind)
    | exact resolve eq12 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq947 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq949 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq950 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq988 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq922 X0 X1
       have j1 := eq127 X0 (σ X1)
       grind)
    | (have r₁ := eq922 X0 X0
       have r₂ := eq127 X0 (σ X0)
       grind)
    | (have r₁ := eq922 X0 X1
       have r₂ := eq127 X0 (σ X1)
       grind)
    | exact resolve eq922 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq922
  have eq1047 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq988 X0 X1
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq988
    | (have j0 := eq988 X0 X1
       grind)
    | exact resolve eq988 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq1088 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1047 X0 X1
       have i₂ := eq38 X1
       grind)
    | exact superpose eq38 eq1047
    | (have j0 := eq1047 X0 X1
       grind)
    | exact resolve eq1047 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047
  have eq1113 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1088 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1088
    | (have j0 := eq1088 X0 X1
       grind)
    | exact resolve eq1088 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088
  have eq4794 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq280 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq280
    | exact resolve eq280 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq4989 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4794 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4794
    | (have j0 := eq4794 X0 X1
       grind)
    | exact resolve eq4794 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4794
  have eq5374 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq334 X0 X1
       have i₂ := eq312 X0 X1
       grind)
    | exact superpose eq312 eq334
    | (have j0 := eq334 X0 X1
       have j1 := eq312 X0 X1
       grind)
    | (have r₁ := eq334 X0 X1
       have r₂ := eq312 X0 X1
       grind)
    | exact resolve eq334 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312 eq334
  have eq5528 : ∀ X0 X1 : G, (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq5374 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5374
  have eq6125 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 (τ X1))) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X1
       have i₂ := eq76 X0 X1
       grind)
    | (have i₁ := eq40 X1
       have i₂ := eq76 (τ X1) X1
       grind)
    | exact superpose eq76 eq40
    | (have j1 := eq76 X0 X1
       grind)
    | exact resolve eq40 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq9478 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1113 (τ X1) (τ X0)
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq1113
    | (have j0 := eq1113 (τ X0) (τ X1)
       grind)
    | exact resolve eq1113 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113
  have eq9563 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9478 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq9478
    | (have j0 := eq9478 X0 X1
       grind)
    | exact resolve eq9478 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9478
  have eq9595 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9563 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq9563
    | (have j0 := eq9563 X0 X1
       grind)
    | exact resolve eq9563 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9563
  have eq9618 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9595 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq9595
    | (have j0 := eq9595 X0 X1
       grind)
    | exact resolve eq9595 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9595
  have eq9635 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9618 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq9618
    | (have j0 := eq9618 X0 X1
       grind)
    | exact resolve eq9618 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9618
  have eq9644 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9635 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9635
    | (have j0 := eq9635 X0 X1
       grind)
    | exact resolve eq9635 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9635
  have eq9649 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9644 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq9644
    | (have j0 := eq9644 X0 X1
       grind)
    | exact resolve eq9644 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9644
  have eq9650 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9649 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq9649
    | (have j0 := eq9649 X0 X1
       grind)
    | exact resolve eq9649 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9649
  have eq11507 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq317 X0 X1
       grind)
    | exact superpose eq317 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq317 X0 X1
       grind)
    | exact resolve eq13 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq11658 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11507 X0 X1
       have i₂ := eq38 X1
       grind)
    | exact superpose eq38 eq11507
    | (have j0 := eq11507 X0 X1
       grind)
    | exact resolve eq11507 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11507
  have eq11783 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11658 X0 X1
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq11658
    | (have j0 := eq11658 X0 X1
       grind)
    | exact resolve eq11658 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11658
  have eq11784 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq11783 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11783
  have eq11870 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11784 X0 X1
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq11784
    | (have j0 := eq11784 X0 X1
       grind)
    | exact resolve eq11784 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11784
  have eq11896 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11870 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq11870
    | (have j0 := eq11870 X0 X1
       grind)
    | exact resolve eq11870 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11870
  have eq11897 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq11896 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11896
  have eq13636 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq947 (τ X0) (τ X1)
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq947
    | (have j0 := eq947 (τ X1) (τ X0)
       grind)
    | exact resolve eq947 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq13741 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13636 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq13636
    | (have j0 := eq13636 X0 X1
       grind)
    | exact resolve eq13636 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13636
  have eq13781 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13741 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq13741
    | (have j0 := eq13741 X0 X1
       grind)
    | exact resolve eq13741 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13741
  have eq13812 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13781 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13781
    | (have j0 := eq13781 X0 X1
       grind)
    | exact resolve eq13781 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13781
  have eq13836 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13812 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq13812
    | (have j0 := eq13812 X0 X1
       grind)
    | exact resolve eq13812 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13812
  have eq13858 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13836 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq13836
    | (have j0 := eq13836 X0 X1
       grind)
    | exact resolve eq13836 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13836
  have eq13877 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13858 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13858
    | (have j0 := eq13858 X0 X1
       grind)
    | exact resolve eq13858 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13858
  have eq13883 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13877 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq13877
    | (have j0 := eq13877 X0 X1
       grind)
    | exact resolve eq13877 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13877
  have eq13889 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13883 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq13883
    | (have j0 := eq13883 X0 X1
       grind)
    | exact resolve eq13883 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13883
  have eq86059 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X1)) X0) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq5528 X1 (τ X0)
       grind)
    | exact superpose eq5528 eq18
    | (have j1 := eq5528 X1 (τ X0)
       grind)
    | exact resolve eq18 eq5528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq86098 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq5528 (σ X0) X1
       grind)
    | exact superpose eq5528 eq28
    | (have j1 := eq5528 (σ X0) X1
       grind)
    | exact resolve eq28 eq5528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5528
  have eq86137 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq86098 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq86098
    | (have j0 := eq86098 X0 X1
       grind)
    | exact resolve eq86098 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86098
  have eq86146 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86059 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq86059
    | (have j0 := eq86059 X0 X1
       grind)
    | exact resolve eq86059 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86059
  have eq86174 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq86137 X0 X1
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq86137
    | (have j0 := eq86137 X0 X1
       grind)
    | exact resolve eq86137 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86137
  have eq86179 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86146 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq86146
    | (have j0 := eq86146 X0 X1
       grind)
    | exact resolve eq86146 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq86146
  have eq86200 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq86174 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq86174
    | (have j0 := eq86174 X0 X1
       grind)
    | exact resolve eq86174 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86174
  have eq86205 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86179 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq86179
    | (have j0 := eq86179 X0 X1
       grind)
    | exact resolve eq86179 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86179
  have eq86216 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq86200 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq86200
    | (have j0 := eq86200 X0 X1
       grind)
    | exact resolve eq86200 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86200
  have eq86219 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq86205 X0 X1
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq86205
    | (have j0 := eq86205 X0 X1
       grind)
    | exact resolve eq86205 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq86205
  have eq86223 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq86216 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq86216
    | (have j0 := eq86216 X0 X1
       grind)
    | exact resolve eq86216 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86216
  have eq88060 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq86223 (σ X0) X1
       grind)
    | exact superpose eq86223 eq28
    | (have j1 := eq86223 (σ X0) X1
       grind)
    | exact resolve eq28 eq86223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86223
  have eq88117 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq88060 X0 X1
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq88060
    | (have j0 := eq88060 X0 X1
       grind)
    | exact resolve eq88060 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88060
  have eq88267 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ X1)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq88117 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq88117
    | (have j0 := eq88117 X0 X1
       grind)
    | exact resolve eq88117 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88117
  have eq97042 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9650 X1 X0
       have i₂ := eq86219 X0 X1
       grind)
    | exact superpose eq86219 eq9650
    | (have j0 := eq9650 X0 X1
       have j1 := eq86219 X1 X0
       grind)
    | (have r₁ := eq9650 X1 X0
       have r₂ := eq86219 X0 X1
       grind)
    | (have r₁ := eq9650 X1 X1
       have r₂ := eq86219 X1 X1
       grind)
    | exact resolve eq9650 eq86219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9650
  have eq97147 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq86219 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86219
  have eq97163 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq97042 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97042
  have eq97266 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq97163 X0 X1
       have j1 := eq97147 X0 X1
       grind)
    | (have r₁ := eq97163 X0 X1
       have r₂ := eq97147 X0 X1
       grind)
    | (have r₁ := eq97163 X1 X0
       have r₂ := eq97147 X0 X1
       grind)
    | (have r₁ := eq97163 X1 X1
       have r₂ := eq97147 X1 X1
       grind)
    | exact resolve eq97163 eq97147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97147 eq97163
  have eq113779 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq97266 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq97266
    | (have j0 := eq97266 (σ X0) X1
       grind)
    | exact resolve eq97266 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97266
  have eq113835 : ∀ X0 X1 : G, (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq113779 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq113779
    | (have j0 := eq113779 X0 X1
       grind)
    | exact resolve eq113779 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq113779
  have eq160979 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq88267 X1 (σ X0)
       grind)
    | exact superpose eq88267 eq22
    | (have j1 := eq88267 X1 (σ X0)
       grind)
    | exact resolve eq22 eq88267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88267
  have eq160990 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq160979 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq160979
    | (have j0 := eq160979 X0 X1
       grind)
    | exact resolve eq160979 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160979
  have eq161026 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq160990 X0 X1
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq160990
    | (have j0 := eq160990 X0 X1
       grind)
    | exact resolve eq160990 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160990
  have eq161056 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq161026 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq161026
    | (have j0 := eq161026 X0 X1
       grind)
    | exact resolve eq161026 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161026
  have eq161077 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq161056 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq161056
    | (have j0 := eq161056 X0 X1
       grind)
    | exact resolve eq161056 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161056
  have eq161089 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq161077 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq161077
    | (have j0 := eq161077 X0 X1
       grind)
    | exact resolve eq161077 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161077
  have eq175995 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq161089 x y
       grind)
    | exact superpose eq161089 eq16
    | (have j1 := eq161089 x y
       grind)
    | exact resolve eq16 eq161089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161089
  have eq178825 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq175995
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq175995
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq175995 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178830 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq175995
       have i₂ := eq4989 x y
       grind)
    | exact superpose eq4989 eq175995
    | (have j1 := eq4989 x y
       grind)
    | (have r₁ := eq175995
       have r₂ := eq4989 x y
       grind)
    | exact resolve eq175995 eq4989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4989 eq175995
  have eq178837 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq178830
  have eq178838 : (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq178837
  have eq178843 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq178825
  have eq178844 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq178843
  have eq178846 : (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq178838
       have r₂ := eq12 y x
       grind)
    | exact resolve eq178838 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178838
  have eq221029 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq113835 X1 (σ X0)
       grind)
    | exact superpose eq113835 eq22
    | (have j1 := eq113835 X1 (σ X0)
       grind)
    | exact resolve eq22 eq113835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq113835
  have eq221034 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq221029 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq221029
    | (have j0 := eq221029 X0 X1
       grind)
    | exact resolve eq221029 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221029
  have eq221046 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq221034 X0 X1
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq221034
    | (have j0 := eq221034 X0 X1
       grind)
    | exact resolve eq221034 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221034
  have eq221053 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq221046 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq221046
    | (have j0 := eq221046 X0 X1
       grind)
    | exact resolve eq221046 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221046
  have eq221057 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq221053 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq221053
    | (have j0 := eq221053 X0 X1
       grind)
    | exact resolve eq221053 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221053
  have eq221058 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq221057 X0 X1
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq221057
    | (have j0 := eq221057 X0 X1
       grind)
    | exact resolve eq221057 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221057
  have eq225809 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq221058 x y
       grind)
    | exact superpose eq221058 eq16
    | (have j1 := eq221058 x y
       grind)
    | exact resolve eq16 eq221058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221058
  have eq288827 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq140 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq140
    | exact resolve eq140 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq288873 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq288827 X0 X1
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq288827
    | (have j0 := eq288827 X0 X1
       grind)
    | exact resolve eq288827 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288827
  have eq295945 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq225809
       have i₂ := eq288873 x y
       grind)
    | exact superpose eq288873 eq225809
    | (have j1 := eq288873 x y
       grind)
    | (have r₁ := eq225809
       have r₂ := eq288873 x y
       grind)
    | exact resolve eq225809 eq288873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225809 eq288873
  have eq296011 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq295945
  have eq296012 : (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq296011
  have eq296036 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have j1 := eq13889 y x
       grind)
    | (have r₁ := eq296012
       have r₂ := eq13889 y x
       grind)
    | exact resolve eq296012 eq13889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13889 eq296012
  have eq296732 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq296036
       have i₂ := eq178846
       grind)
    | exact superpose eq178846 eq296036
    | exact resolve eq296036 eq178846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178846 eq296036
  have eq296764 : (M.op x y) = (M.op y y) ∨ (M.op x x) = (k y x) := by grind
  clear eq296732
  have eq296769 : (M.op x x) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq296764
       have r₂ := eq12 y x
       grind)
    | exact resolve eq296764 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296764
  have eq297555 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq949 x y
       have i₂ := eq296769
       grind)
    | exact superpose eq296769 eq949
    | (have j0 := eq949 x y
       grind)
    | exact resolve eq949 eq296769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq297556 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq950 x y
       have i₂ := eq296769
       grind)
    | exact superpose eq296769 eq950
    | (have j0 := eq950 x y
       grind)
    | exact resolve eq950 eq296769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq297581 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq297556
  have eq297582 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq297555
  have eq310852 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq297581
       grind)
    | exact superpose eq297581 eq16
    | exact resolve eq16 eq297581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297581
  have eq311471 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq310852
       have i₂ := eq178844
       grind)
    | exact superpose eq178844 eq310852
    | exact resolve eq310852 eq178844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178844 eq310852
  have eq311473 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq311471
  have eq318240 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq311473
       grind)
    | exact superpose eq311473 eq16
    | exact resolve eq16 eq311473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1788442 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X1 X0)) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6125 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6125
    | exact resolve eq6125 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6125
  have eq1788448 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1788442 X0 X1
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq1788442
    | (have j0 := eq1788442 X0 X1
       grind)
    | exact resolve eq1788442 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq1788442
  have eq1788451 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1788448 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1788448
    | (have j0 := eq1788448 X0 X1
       grind)
    | exact resolve eq1788448 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1788448
  have eq1788456 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1788451 y x
       have i₂ := eq296769
       grind)
    | exact superpose eq296769 eq1788451
    | (have j0 := eq1788451 y x
       grind)
    | exact resolve eq1788451 eq296769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1788451
  have eq1788469 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq1788456
       have r₂ := eq318240
       grind)
    | exact resolve eq1788456 eq318240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1788456
  have eq1788834 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq11897 y x
       have i₂ := eq296769
       grind)
    | exact superpose eq296769 eq11897
    | (have j0 := eq11897 y x
       grind)
    | exact resolve eq11897 eq296769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11897
  have eq1788835 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq1788834
  have eq1788837 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq311473
       have i₂ := eq1788835
       grind)
    | exact superpose eq1788835 eq311473
    | exact resolve eq311473 eq1788835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311473 eq1788835
  have eq1788841 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq1788837
  have eq1788858 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1788469
       have i₂ := eq1788841
       grind)
    | exact superpose eq1788841 eq1788469
    | exact resolve eq1788469 eq1788841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1788469 eq1788841
  have eq1788883 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq1788858
  have eq1788905 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq1788883
       have r₂ := eq318240
       grind)
    | exact resolve eq1788883 eq318240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318240 eq1788883
  have eq1788925 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1788905
       grind)
    | exact superpose eq1788905 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1788905
       grind)
    | exact resolve eq13 eq1788905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1788946 : (M.op x x) = (M.op y y) ∨ (M.op y y) = (k y x) := by grind
  clear eq1788925
  have eq1788949 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq1788946
       have i₂ := eq296769
       grind)
    | exact superpose eq296769 eq1788946
    | exact resolve eq1788946 eq296769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296769 eq1788946
  have eq1788950 : (M.op x x) = (M.op y y) := by grind
  clear eq1788949
  have eq1788973 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq297582
       have i₂ := eq1788950
       grind)
    | exact superpose eq1788950 eq297582
    | exact resolve eq297582 eq1788950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297582 eq1788950
  have eq1789194 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq1788973
  have eq1789228 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1789194
       grind)
    | exact superpose eq1789194 eq16
    | exact resolve eq16 eq1789194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1789194
  have eq1789254 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1789228
       have i₂ := eq1788905
       grind)
    | exact superpose eq1788905 eq1789228
    | exact resolve eq1789228 eq1788905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1788905 eq1789228
  have eq1789255 : False := by grind
  exact eq1789255

/-- `Equation4293`: `x ◇ (x ◇ y) = y ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,X) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyx_pxx_pyy_pyx_Equation4293 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4293 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4293.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq33 (σ X0)
       grind)
    | exact superpose eq33 eq15
    | exact resolve eq15 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq33 (τ X0)
       grind)
    | exact superpose eq33 eq18
    | exact resolve eq18 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq37
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq40 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq35
    | exact resolve eq35 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq42 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq38
    | exact resolve eq38 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq38
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq62 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq79 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq84 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq86 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq75
    | (have j0 := eq75 X0 X1
       grind)
    | exact resolve eq75 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq88 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       have j1 := eq80 X1 X0
       grind)
    | (have r₁ := eq82 X0 X1
       have r₂ := eq80 X0 X1
       grind)
    | (have r₁ := eq82 X1 X0
       have r₂ := eq80 X0 X1
       grind)
    | (have r₁ := eq82 X0 X0
       have r₂ := eq80 X0 X0
       grind)
    | exact resolve eq82 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq82
  have eq91 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq126 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq10
    | exact resolve eq10 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq88 X1 (τ X0)
       grind)
    | exact superpose eq88 eq18
    | (have j1 := eq88 X1 (τ X0)
       grind)
    | exact resolve eq18 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq88
  have eq294 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq274 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq274
    | (have j0 := eq274 X0 X1
       grind)
    | exact resolve eq274 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq311 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq294 X0 X1
       have i₂ := eq147 X0
       grind)
    | exact superpose eq147 eq294
    | (have j0 := eq294 X0 X1
       grind)
    | exact resolve eq294 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq334 : ∀ X0 X1 : G, (M.op (τ X0) X1) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq147 X0
       grind)
    | exact superpose eq147 eq12
    | (have j0 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq12 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq1010 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq91 X1 X0
       grind)
    | exact superpose eq91 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq91 X1 X0
       grind)
    | exact resolve eq12 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1039 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1040 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq1080 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1010 X0 X1
       have j1 := eq127 X1 (σ X0)
       grind)
    | (have r₁ := eq1010 X0 X0
       have r₂ := eq127 X0 (σ X0)
       grind)
    | (have r₁ := eq1010 X0 X0
       have r₂ := eq127 X0 (σ X0)
       grind)
    | exact resolve eq1010 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq1010
  have eq1141 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1080 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq1080
    | (have j0 := eq1080 X0 X1
       grind)
    | exact resolve eq1080 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080
  have eq1182 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1141 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq1141
    | (have j0 := eq1141 X0 X1
       grind)
    | exact resolve eq1141 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq1207 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1182 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1182
    | (have j0 := eq1182 X0 X1
       grind)
    | exact resolve eq1182 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq6526 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq334 X0 X1
       have i₂ := eq311 X0 X1
       grind)
    | exact superpose eq311 eq334
    | (have j0 := eq334 X0 X1
       have j1 := eq311 X0 X1
       grind)
    | (have r₁ := eq334 X0 X1
       have r₂ := eq311 X0 X1
       grind)
    | exact resolve eq334 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq6568 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq311 X0 X1
       grind)
    | exact superpose eq311 eq11
    | (have j1 := eq311 X0 X1
       grind)
    | exact resolve eq11 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq6694 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq6526 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6526
  have eq10967 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1207 (τ X1) (τ X0)
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq1207
    | (have j0 := eq1207 (τ X0) (τ X1)
       grind)
    | exact resolve eq1207 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11056 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10967 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq10967
    | (have j0 := eq10967 X0 X1
       grind)
    | exact resolve eq10967 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10967
  have eq11086 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11056 X0 X1
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq11056
    | (have j0 := eq11056 X0 X1
       grind)
    | exact resolve eq11056 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11056
  have eq11112 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11086 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq11086
    | (have j0 := eq11086 X0 X1
       grind)
    | exact resolve eq11086 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11086
  have eq11128 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11112 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq11112
    | (have j0 := eq11112 X0 X1
       grind)
    | exact resolve eq11112 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11112
  have eq11138 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11128 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11128
    | (have j0 := eq11128 X0 X1
       grind)
    | exact resolve eq11128 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11128
  have eq11143 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11138 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq11138
    | (have j0 := eq11138 X0 X1
       grind)
    | exact resolve eq11138 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11138
  have eq11144 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11143 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq11143
    | (have j0 := eq11143 X0 X1
       grind)
    | exact resolve eq11143 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11143
  have eq80778 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (τ X1)) (σ X0)) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1040 (τ X1) X0
       have i₂ := eq6694 X1 X0
       grind)
    | exact superpose eq6694 eq1040
    | (have j0 := eq1040 (τ X1) X0
       have j1 := eq6694 X1 X0
       grind)
    | exact resolve eq1040 eq6694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040
  have eq80826 : ∀ X0 X1 : G, (k X0 (σ (τ X1))) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq6694 X1 (τ X0)
       grind)
    | exact superpose eq6694 eq17
    | (have j1 := eq6694 X1 (τ X0)
       grind)
    | exact resolve eq17 eq6694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq81208 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq6694 (σ X0) X1
       grind)
    | exact superpose eq6694 eq22
    | (have j1 := eq6694 (σ X0) X1
       grind)
    | exact resolve eq22 eq6694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6694
  have eq81307 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (τ X1)) (σ X0)) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq80778 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80778
  have eq81424 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq81208 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq81208
    | (have j0 := eq81208 X0 X1
       grind)
    | exact resolve eq81208 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81208
  have eq81586 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ (τ X1))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq80826 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq80826
    | (have j0 := eq80826 X0 X1
       grind)
    | exact resolve eq80826 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80826
  have eq81623 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ X0)) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq81307 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq81307
    | (have j0 := eq81307 X0 X1
       grind)
    | exact resolve eq81307 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81307
  have eq81856 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq81424 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq81424
    | (have j0 := eq81424 X0 X1
       grind)
    | exact resolve eq81424 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81424
  have eq81943 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq81586 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq81586
    | (have j0 := eq81586 X0 X1
       grind)
    | exact resolve eq81586 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81586
  have eq81976 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op X0 X0)) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq81623 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq81623
    | (have j0 := eq81623 X0 X1
       grind)
    | exact resolve eq81623 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81623
  have eq82110 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq81856 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq81856
    | (have j0 := eq81856 X0 X1
       grind)
    | exact resolve eq81856 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81856
  have eq82175 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq81943 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81943
    | (have j0 := eq81943 X0 X1
       grind)
    | exact resolve eq81943 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81943
  have eq82200 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq81976 X0 X1
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq81976
    | (have j0 := eq81976 X0 X1
       grind)
    | exact resolve eq81976 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq81976
  have eq82275 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq82110 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq82110
    | (have j0 := eq82110 X0 X1
       grind)
    | exact resolve eq82110 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82110
  have eq82330 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq82175 X0 X1
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq82175
    | (have j0 := eq82175 X0 X1
       grind)
    | exact resolve eq82175 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq82175
  have eq82331 : ∀ X0 X1 : G, (M.op X1 X1) = (k (σ X0) X1) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq82200 X0 X1
       have j1 := eq126 X0 X1
       grind)
    | (have r₁ := eq82200 X0 X1
       have r₂ := eq126 X0 X1
       grind)
    | exact resolve eq82200 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq82200
  have eq82377 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq82275 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq82275
    | (have j0 := eq82275 X0 X1
       grind)
    | exact resolve eq82275 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82275
  have eq84019 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq82377 (σ X0) X1
       grind)
    | exact superpose eq82377 eq22
    | (have j1 := eq82377 (σ X0) X1
       grind)
    | exact resolve eq22 eq82377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82377
  have eq84486 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq84019 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq84019
    | (have j0 := eq84019 X0 X1
       grind)
    | exact resolve eq84019 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84019
  have eq84753 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq84486 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq84486
    | (have j0 := eq84486 X0 X1
       grind)
    | exact resolve eq84486 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84486
  have eq87722 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11144 X0 X1
       have i₂ := eq82330 X0 X1
       grind)
    | exact superpose eq82330 eq11144
    | (have j0 := eq11144 X1 X0
       have j1 := eq82330 X1 X0
       grind)
    | (have r₁ := eq11144 X0 X1
       have r₂ := eq82330 X0 X1
       grind)
    | (have r₁ := eq11144 X1 X1
       have r₂ := eq82330 X1 X1
       grind)
    | exact resolve eq11144 eq82330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87827 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq82330 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82330
  have eq87842 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq87722 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87722
  have eq87943 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq87842 X0 X1
       have j1 := eq87827 X1 X0
       grind)
    | (have r₁ := eq87842 X0 X1
       have r₂ := eq87827 X0 X1
       grind)
    | (have r₁ := eq87842 X1 X0
       have r₂ := eq87827 X0 X1
       grind)
    | (have r₁ := eq87842 X0 X0
       have r₂ := eq87827 X0 X0
       grind)
    | exact resolve eq87842 eq87827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87827 eq87842
  have eq105257 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (k X1 (σ X0))) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq87943 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq87943
    | (have j0 := eq87943 (σ X0) X1
       grind)
    | exact resolve eq87943 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87943
  have eq105315 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq105257 X0 X1
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq105257
    | (have j0 := eq105257 X0 X1
       grind)
    | exact resolve eq105257 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq105257
  have eq126840 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq82331 X0 (σ X0)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq82331
    | (have j0 := eq82331 X1 (σ X0)
       grind)
    | exact resolve eq82331 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82331
  have eq126876 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq126840 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq126840
    | (have j0 := eq126840 X0 X1
       grind)
    | exact resolve eq126840 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126840
  have eq126884 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq126876 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq126876
    | (have j0 := eq126876 X0 X1
       grind)
    | exact resolve eq126876 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126876
  have eq149582 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq84753 X1 (σ X0)
       grind)
    | exact superpose eq84753 eq28
    | (have j1 := eq84753 X1 (σ X0)
       grind)
    | exact resolve eq28 eq84753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84753
  have eq149631 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq149582 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq149582
    | (have j0 := eq149582 X0 X1
       grind)
    | exact resolve eq149582 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149582
  have eq149656 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq149631 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq149631
    | (have j0 := eq149631 X0 X1
       grind)
    | exact resolve eq149631 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149631
  have eq149673 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq149656 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq149656
    | (have j0 := eq149656 X0 X1
       grind)
    | exact resolve eq149656 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149656
  have eq149686 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq149673 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq149673
    | (have j0 := eq149673 X0 X1
       grind)
    | exact resolve eq149673 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149673
  have eq149691 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq149686 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq149686
    | (have j0 := eq149686 X0 X1
       grind)
    | exact resolve eq149686 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149686
  have eq158784 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq149691 y x
       grind)
    | exact superpose eq149691 eq16
    | (have j1 := eq149691 y x
       grind)
    | exact resolve eq16 eq149691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149691
  have eq162121 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq158784
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq158784
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq158784 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158784
  have eq162139 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq162121
  have eq162140 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq162139
  have eq208903 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq105315 X1 (σ X0)
       grind)
    | exact superpose eq105315 eq28
    | (have j1 := eq105315 X1 (σ X0)
       grind)
    | exact resolve eq28 eq105315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq105315
  have eq208908 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq208903 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq208903
    | (have j0 := eq208903 X0 X1
       grind)
    | exact resolve eq208903 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208903
  have eq208924 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq208908 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq208908
    | (have j0 := eq208908 X0 X1
       grind)
    | exact resolve eq208908 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208908
  have eq208935 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq208924 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq208924
    | (have j0 := eq208924 X0 X1
       grind)
    | exact resolve eq208924 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208924
  have eq208941 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq208935 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq208935
    | (have j0 := eq208935 X0 X1
       grind)
    | exact resolve eq208935 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208935
  have eq208942 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq208941 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq208941
    | (have j0 := eq208941 X0 X1
       grind)
    | exact resolve eq208941 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208941
  have eq216288 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (k y x) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq208942 y x
       grind)
    | exact superpose eq208942 eq16
    | (have j1 := eq208942 y x
       grind)
    | exact resolve eq16 eq208942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208942
  have eq374865 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6568 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6568
    | (have j0 := eq6568 (σ X0) X1
       grind)
    | exact resolve eq6568 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6568
  have eq374901 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq374865 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq374865
    | (have j0 := eq374865 X0 X1
       grind)
    | exact resolve eq374865 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374865
  have eq374905 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq374901 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq374901
    | (have j0 := eq374901 X0 X1
       grind)
    | exact resolve eq374901 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq374901
  have eq374909 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq374905 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq374905
    | (have j0 := eq374905 X0 X1
       grind)
    | exact resolve eq374905 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374905
  have eq667670 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq126884 x y
       grind)
    | exact superpose eq126884 eq16
    | (have j1 := eq126884 x y
       grind)
    | exact resolve eq16 eq126884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126884
  have eq667675 : (σ (M.op x x)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have j1 := eq374909 x y
       grind)
    | (have r₁ := eq667670
       have r₂ := eq374909 x y
       grind)
    | exact resolve eq667670 eq374909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374909 eq667670
  have eq677014 : (k y x) = (τ (σ (M.op x x))) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq667675
       grind)
    | exact superpose eq667675 eq10
    | exact resolve eq10 eq667675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667675
  have eq677060 : (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq677014
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq677014
    | exact resolve eq677014 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677014
  have eq686612 : (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq677060
       have i₂ := eq84 x y
       grind)
    | exact superpose eq84 eq677060
    | (have j1 := eq84 x y
       grind)
    | exact resolve eq677060 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq686624 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (k y x) := by grind
  clear eq677060
  have eq686632 : (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (M.op x y) = (k y x) := by grind
  clear eq686612
  have eq686636 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have j1 := eq79 x y
       grind)
    | (have r₁ := eq686632
       have r₂ := eq79 x y
       grind)
    | (have r₁ := eq686632
       have r₂ := eq79 y x
       grind)
    | exact resolve eq686632 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq686632
  have eq703135 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq11144 y x
       have i₂ := eq686636
       grind)
    | exact superpose eq686636 eq11144
    | (have j0 := eq11144 y x
       grind)
    | exact resolve eq11144 eq686636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11144 eq686636
  have eq703153 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq703135
  have eq703160 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq703153
       have r₂ := eq162140
       grind)
    | exact resolve eq703153 eq162140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162140 eq703153
  have eq715885 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq216288
       have i₂ := eq703160
       grind)
    | exact superpose eq703160 eq216288
    | exact resolve eq216288 eq703160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216288
  have eq715889 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq703160
       grind)
    | exact superpose eq703160 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq703160
       grind)
    | exact resolve eq13 eq703160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq716064 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k y x) := by grind
  clear eq715885
  have eq716065 : (M.op x y) = (k y x) := by grind
  clear eq716064
  have eq728082 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1039 x y
       have i₂ := eq716065
       grind)
    | exact superpose eq716065 eq1039
    | (have j0 := eq1039 x y
       grind)
    | exact resolve eq1039 eq716065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039 eq716065
  have eq728106 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq728082
       have r₂ := eq16
       grind)
    | exact resolve eq728082 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728082
  have eq728112 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq728106
       have i₂ := eq703160
       grind)
    | exact superpose eq703160 eq728106
    | exact resolve eq728106 eq703160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728106
  have eq728117 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have r₁ := eq728112
       have r₂ := eq16
       grind)
    | exact resolve eq728112 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728112
  have eq778768 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by
    first
    | (have j0 := eq715889 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715889
  have eq778769 : (M.op x x) = (k y x) := by
    first
    | (have r₁ := eq778768
       have r₂ := eq686624
       grind)
    | exact resolve eq778768 eq686624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686624 eq778768
  have eq781751 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1207 y x
       have i₂ := eq778769
       grind)
    | exact superpose eq778769 eq1207
    | (have j0 := eq1207 y x
       grind)
    | exact resolve eq1207 eq778769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207 eq778769
  have eq781782 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq781751
  have eq781795 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq781782
       have i₂ := eq703160
       grind)
    | exact superpose eq703160 eq781782
    | exact resolve eq781782 eq703160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781782
  have eq781796 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq781795
       have r₂ := eq728117
       grind)
    | exact resolve eq781795 eq728117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728117 eq781795
  have eq781797 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq781796
       have i₂ := eq703160
       grind)
    | exact superpose eq703160 eq781796
    | exact resolve eq781796 eq703160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703160 eq781796
  have eq781798 : False := by grind
  exact eq781798

/-- `Equation433`: `x = x ◇ (y ◇ (x ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxy_x_pyx_Equation433 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law433 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law433.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 (M.op X0 (M.op X3 X2))) (M.op X1 X0))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op X2 (M.op X0 (M.op X3 X2))) X0
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
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
  have eq29 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X2 X0) X0
       have i₂ := eq25 X2 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq42 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 X2) (M.op X2 X0)) ∨ (k X0 (M.op X1 X2)) = (M.op (M.op X1 X2) X0) ∨ (M.op X1 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X2) X2 X1
       have i₂ := eq14 X0 (M.op X1 X2)
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 (M.op X0 (M.op X2 X1)) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 (M.op X1 X2)
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq65 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq50
    | exact resolve eq50 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  clear eq50
  have eq75 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq27 (σ X0) (σ X0)
       grind)
    | exact superpose eq27 eq71
    | exact resolve eq71 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq131 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 (M.op X3 X1))) (M.op X0 X2)) = (M.op (M.op (M.op X1 (M.op X2 (M.op X3 X1))) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X0 (M.op (M.op X1 (M.op X2 (M.op X3 X1))) (M.op X0 X2))
       have i₂ := eq23 X2 X0 X1 X3
       grind)
    | exact superpose eq23 eq25
    | exact resolve eq25 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq173 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 X2)) = (M.op (M.op (M.op X1 X2) (M.op X0 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X0 (M.op (M.op X1 X2) (M.op X0 X2))
       have i₂ := eq29 X2 X0 X1
       grind)
    | exact superpose eq29 eq25
    | exact resolve eq25 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq363 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38 x y
       grind)
    | exact superpose eq38 eq16
    | (have j1 := eq38 x y
       grind)
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq364 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ X0) (M.op X2 (σ (k X0 X1))))) = X2 ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X0) (σ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq9
    | (have j1 := eq38 X1 X0
       grind)
    | exact resolve eq9 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (M.op (σ X0) (σ X0)) (σ X2)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X2
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq15
    | (have j1 := eq38 X0 X1
       grind)
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq389 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X1) (σ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq25
    | (have j1 := eq38 X1 X0
       grind)
    | exact resolve eq25 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq482 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) ∨ (M.op X0 X0) = X1 ∨ (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0)
       have i₂ := eq42 X0 X0 X0
       grind)
    | exact superpose eq42 eq14
    | (have j0 := eq14 X1 (M.op X0 X0)
       have j1 := eq42 X1 X0 X0
       grind)
    | exact resolve eq14 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq487 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 X2) (M.op X0 X1)) ∨ (k X2 (M.op X0 X1)) = (M.op (M.op X0 X1) X2) ∨ (M.op X0 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 (M.op X0 X1) (M.op X1 X2)
       have i₂ := eq42 X2 X0 X1
       grind)
    | exact superpose eq42 eq25
    | (have j1 := eq42 X2 X0 X1
       grind)
    | exact resolve eq25 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq492 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq482 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq497 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq492 X0 X1
       have i₂ := eq27 X0 X0
       grind)
    | exact superpose eq27 eq492
    | (have j0 := eq492 X0 X1
       grind)
    | exact resolve eq492 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq3107 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq363
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq363
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq363
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq363
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq363 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq3108 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq3107
  have eq6855 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq389 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq8304 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (τ X0)) (M.op X2 (σ (τ (k X0 X1)))))) = X2 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq364 (τ X0) (τ X1) X2
       have i₂ := eq65 X1 X0
       grind)
    | exact superpose eq65 eq364
    | (have j0 := eq364 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq364 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq8674 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (τ X0)) (M.op X2 (k X0 X1)))) = X2 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8304 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq8304
    | (have j0 := eq8304 X0 X1 X2
       grind)
    | exact resolve eq8304 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8304
  have eq8705 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X2 (k X0 X1)))) = X2 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8674 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8674
    | (have j0 := eq8674 X0 X1 X2
       grind)
    | exact resolve eq8674 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8674
  have eq8709 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X2 (M.op X0 (M.op X2 (k X0 X1)))) = X2 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8705 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8705
    | (have j0 := eq8705 X0 X1 X2
       grind)
    | exact resolve eq8705 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8705
  have eq8710 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X0 ∨ (M.op X2 (M.op X0 (M.op X2 (k X0 X1)))) = X2 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8709 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8709
    | (have j0 := eq8709 X0 X1 X2
       grind)
    | exact resolve eq8709 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8709
  have eq8711 : ∀ X0 X1 X2 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X2 (M.op X0 (M.op X2 (k X0 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8710 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq8710
    | (have j0 := eq8710 X0 X1 X2
       grind)
    | exact resolve eq8710 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8710
  have eq8712 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X2 (k X0 X1)))) = X2 ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8711 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8711
    | (have j0 := eq8711 X0 X1 X2
       grind)
    | exact resolve eq8711 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8711
  have eq10873 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = (M.op (M.op X0 (M.op X0 (M.op X1 X0))) X2) ∨ (k (M.op X0 (M.op X1 X0)) (M.op X2 X0)) = (M.op (M.op X2 X0) (M.op X0 (M.op X1 X0))) ∨ (M.op X2 X0) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq131 X0 X1 X1 x
       have i₂ := eq487 X0 X1 (M.op X1 (M.op x X1))
       grind)
    | exact superpose eq487 eq131
    | (have j1 := eq487 X2 X0 (M.op X0 (M.op X1 X0))
       grind)
    | exact resolve eq131 eq487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq487
  have eq10981 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X2) ∨ (k (M.op X0 (M.op X1 X0)) (M.op X2 X0)) = (M.op (M.op X2 X0) (M.op X0 (M.op X1 X0))) ∨ (M.op X2 X0) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10873 X1 X0 X2
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq10873
    | (have j0 := eq10873 X0 X1 X2
       grind)
    | exact resolve eq10873 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10873
  have eq11002 : ∀ X0 X1 X2 : G, (k X0 (M.op X2 X0)) = (M.op (M.op X2 X0) X0) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X2) ∨ (M.op X2 X0) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10981 X1 X0 X2
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq10981
    | (have j0 := eq10981 X0 X1 X2
       grind)
    | exact resolve eq10981 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10981
  have eq11011 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X0 (M.op X2 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X2) ∨ (M.op X2 X0) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11002 X0 X1 X2
       have i₂ := eq27 X0 X2
       grind)
    | exact superpose eq27 eq11002
    | (have j0 := eq11002 X0 X1 X2
       grind)
    | exact resolve eq11002 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11002
  have eq11020 : ∀ X0 X2 : G, (M.op X2 X0) = (k X0 (M.op X2 X0)) ∨ (M.op X2 X0) = X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq11011 X0 x X2
       have i₂ := eq25 x X0
       grind)
    | exact superpose eq25 eq11011
    | (have j0 := eq11011 X0 x X2
       grind)
    | exact resolve eq11011 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11011
  have eq11948 : ∀ X0 X1 X2 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (k X1 X2)) = (k (M.op X0 X0) (σ X2)) ∨ (σ X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq374 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq374
    | exact resolve eq374 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq12222 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (M.op X0 X0) (σ X2)) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11948 X0 X1 X2
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq11948
    | (have j0 := eq11948 X0 X1 X2
       grind)
    | exact resolve eq11948 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq11948
  have eq16765 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq497 X0 (k X0 (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq16766 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq16765 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16765
  have eq16809 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq16766 X0
       have j1 := eq11020 X0 X0
       grind)
    | (have r₁ := eq16766 x
       have r₂ := eq11020 x x
       grind)
    | exact resolve eq16766 eq11020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11020 eq16766
  have eq97067 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq75 x
       have i₂ := eq3108
       grind)
    | exact superpose eq3108 eq75
    | exact resolve eq75 eq3108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3108
  have eq97266 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq97067
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq97067
    | exact resolve eq97067 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97067
  have eq97285 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq97266
       grind)
    | exact superpose eq97266 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq97266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97304 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 y))) = X0 ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8712 y x X0
       have i₂ := eq97266
       grind)
    | exact superpose eq97266 eq8712
    | (have j0 := eq8712 y x x
       grind)
    | exact resolve eq8712 eq97266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8712 eq97266
  have eq97349 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 y))) = X0 ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq97304 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97304
  have eq97368 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq97285
  have eq97381 : ∀ X0 : G, y = (M.op x x) ∨ (M.op X0 y) = X0 ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq97349 X0
       have i₂ := eq25 X0 y
       grind)
    | exact superpose eq25 eq97349
    | exact resolve eq97349 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97349
  have eq99058 : x = y ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq97368
       have i₂ := eq97381 x
       grind)
    | exact superpose eq97381 eq97368
    | exact resolve eq97368 eq97381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97368 eq97381
  have eq99065 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq99058
  have eq99182 : y = (k x y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16809 x
       have i₂ := eq99065
       grind)
    | exact superpose eq99065 eq16809
    | exact resolve eq16809 eq99065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16809
  have eq99193 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq25 x x
       have i₂ := eq99065
       grind)
    | exact superpose eq99065 eq25
    | exact resolve eq25 eq99065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99065
  have eq99291 : y = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq99182
  have eq101487 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6855 y x
       have i₂ := eq99291
       grind)
    | exact superpose eq99291 eq6855
    | (have j0 := eq6855 y x
       grind)
    | exact resolve eq6855 eq99291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6855 eq99291
  have eq101535 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq101487
  have eq101536 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq101535
  have eq107410 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25 (σ y) (σ x)
       have i₂ := eq101536
       grind)
    | exact superpose eq101536 eq25
    | exact resolve eq25 eq101536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101536
  have eq109190 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq107410
       grind)
    | exact superpose eq107410 eq16
    | exact resolve eq16 eq107410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107410
  have eq111271 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq109190
       have i₂ := eq99193
       grind)
    | exact superpose eq99193 eq109190
    | exact resolve eq109190 eq99193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99193 eq109190
  have eq111283 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq111271
  have eq111284 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq111283
  have eq112834 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq111284
       grind)
    | exact superpose eq111284 eq10
    | exact resolve eq10 eq111284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111284
  have eq113005 : x = y ∨ x = y := by
    first
    | (have i₁ := eq112834
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq112834
    | exact resolve eq112834 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112834
  have eq113006 : x = y := by grind
  clear eq113005
  have eq114583 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq113006
       grind)
    | exact superpose eq113006 eq16
    | exact resolve eq16 eq113006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113006
  have eq116158 : ∀ X0 : G, (σ (M.op x x)) ≠ X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = X0 := by
    intro X0
    first
    | (have i₁ := eq114583
       have i₂ := eq14 X0 (σ x)
       grind)
    | (have i₁ := eq114583
       have i₂ := eq14 (M.op (σ x) (σ x)) x
       grind)
    | exact superpose eq14 eq114583
    | (have j1 := eq14 X0 (σ x)
       grind)
    | (have r₁ := eq114583
       have r₂ := eq14 (σ (M.op x x)) (σ x)
       grind)
    | (have r₁ := eq114583
       have r₂ := eq14 (M.op (σ x) (σ x)) (σ (M.op x x))
       grind)
    | (have r₁ := eq114583
       have r₂ := eq14 (σ (M.op x x)) (M.op (σ x) (σ x))
       grind)
    | exact resolve eq114583 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141809 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (M.op X2 X2) (σ (τ X1))) ∨ (k (σ (τ X0)) X2) = (M.op X2 (σ (τ X0))) ∨ (σ (τ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12222 X2 (τ X0) (τ X1)
       have i₂ := eq65 X1 X0
       grind)
    | exact superpose eq65 eq12222
    | (have j0 := eq12222 X2 (τ X0) X2
       grind)
    | exact resolve eq12222 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq12222
  have eq141993 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (M.op X2 X2) X1) ∨ (k (σ (τ X0)) X2) = (M.op X2 (σ (τ X0))) ∨ (σ (τ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq141809 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq141809
    | (have j0 := eq141809 X0 X1 X2
       grind)
    | exact resolve eq141809 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141809
  have eq141999 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (M.op X2 X2) X1) ∨ (k (σ (τ X0)) X2) = (M.op X2 (σ (τ X0))) ∨ (σ (τ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq141993 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq141993
    | (have j0 := eq141993 X0 X1 X2
       grind)
    | exact resolve eq141993 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141993
  have eq142000 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X0 X2) ∨ (k X0 X1) = (k (M.op X2 X2) X1) ∨ (σ (τ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq141999 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq141999
    | (have j0 := eq141999 X0 X1 X2
       grind)
    | exact resolve eq141999 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141999
  have eq142001 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (M.op X2 X2) X1) ∨ (M.op X2 X0) = (k X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq142000 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq142000
    | (have j0 := eq142000 X0 X1 X2
       grind)
    | exact resolve eq142000 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142000
  have eq145414 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq142001 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142001
  have eq145440 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  clear eq145414
  have eq145529 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq145440 X0 X1
       have i₂ := eq27 X1 X1
       grind)
    | exact superpose eq27 eq145440
    | (have j0 := eq145440 X0 X1
       grind)
    | (have r₁ := eq145440 X0 X0
       have r₂ := eq27 X0 X0
       grind)
    | exact resolve eq145440 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145440
  have eq167430 : (k (σ (M.op x x)) (σ x)) = (M.op (σ x) (σ (M.op x x))) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have j0 := eq116158 (σ (M.op x x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116158
  have eq167431 : (M.op (σ x) (σ (M.op x x))) = (σ (k (M.op x x) x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq167430
       have i₂ := eq15 (M.op x x) x
       grind)
    | exact superpose eq15 eq167430
    | exact resolve eq167430 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167430
  have eq167432 : (M.op (σ x) (σ (M.op x x))) = (σ (M.op (M.op x x) x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq167431
  have eq167433 : (σ (M.op x x)) = (M.op (σ x) (σ (M.op x x))) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq167432
       have i₂ := eq27 x x
       grind)
    | exact superpose eq27 eq167432
    | exact resolve eq167432 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq167432
  have eq167472 : ∀ X0 : G, (M.op X0 (M.op (σ (M.op x x)) (M.op X0 (σ (M.op x x))))) = X0 ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq29 (σ (M.op x x)) X0 (σ x)
       have i₂ := eq167433
       grind)
    | exact superpose eq167433 eq29
    | exact resolve eq29 eq167433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq167556 : ∀ X0 : G, (M.op X0 (σ (M.op x x))) = X0 ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq167472 X0
       have i₂ := eq25 X0 (σ (M.op x x))
       grind)
    | exact superpose eq25 eq167472
    | exact resolve eq167472 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167472
  have eq167708 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq167433
       have i₂ := eq167556 (σ x)
       grind)
    | exact superpose eq167556 eq167433
    | exact resolve eq167433 eq167556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167433 eq167556
  have eq167709 : (σ x) = (σ (M.op x x)) := by grind
  clear eq167708
  have eq167743 : (τ (σ x)) = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq167709
       grind)
    | exact superpose eq167709 eq10
    | exact resolve eq10 eq167709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167985 : x = (M.op x x) := by
    first
    | (have i₁ := eq167743
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq167743
    | exact resolve eq167743 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167743
  have eq168103 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op (M.op x (M.op X0 x)) X0) := by
    intro X0
    first
    | (have i₁ := eq173 X0 x x
       have i₂ := eq167985
       grind)
    | exact superpose eq167985 eq173
    | exact resolve eq173 eq167985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq168328 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq168103 X0
       have i₂ := eq25 X0 x
       grind)
    | exact superpose eq25 eq168103
    | exact resolve eq168103 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq168103
  have eq168635 : ∀ X0 : G, x ≠ (M.op x x) ∨ x = (k X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq145529 X0 x
       have i₂ := eq168328 X0
       grind)
    | exact superpose eq168328 eq145529
    | (have j0 := eq145529 x (k X0 x)
       grind)
    | exact resolve eq145529 eq168328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145529 eq168328
  have eq168920 : ∀ X0 : G, x = (k X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq168635 X0
       grind)
    | (have r₁ := eq168635 X0
       have r₂ := eq167985
       grind)
    | exact resolve eq168635 eq167985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167985 eq168635
  have eq169691 : x = (τ (M.op (σ x) (σ x))) ∨ x = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq75 x
       have i₂ := eq168920 (τ (M.op (σ x) (σ x)))
       grind)
    | exact superpose eq168920 eq75
    | (have j1 := eq168920 (τ (M.op (σ x) (σ x)))
       grind)
    | exact resolve eq75 eq168920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq168920
  have eq169731 : x = (τ (M.op (σ x) (σ x))) := by grind
  clear eq169691
  have eq170015 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ x))
       have i₂ := eq169731
       grind)
    | exact superpose eq169731 eq11
    | exact resolve eq11 eq169731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169731
  have eq170808 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq114583
       have i₂ := eq170015
       grind)
    | exact superpose eq170015 eq114583
    | exact resolve eq114583 eq170015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114583 eq170015
  have eq171177 : False := by grind
  exact eq171177

/-- `Equation433`: `x = x ◇ (y ◇ (x ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyy_x_pyx_Equation433 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law433 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law433.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
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
  have eq27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq31 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (M.op X1 X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq31
    | exact resolve eq31 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X2 X0) X0
       have i₂ := eq31 X2 X0
       grind)
    | exact superpose eq31 eq9
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq40 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq42 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X1 X0))) = X1 ∨ (M.op X2 X0) = (k X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 X2
       have i₂ := eq14 X0 X2
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 (M.op X2 X1) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X2
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  have eq55 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = X1 := by
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
  have eq64 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27
    | exact resolve eq27 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  clear eq27
  have eq144 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq40 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq40
    | (have j0 := eq40 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq40 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq207 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (M.op (M.op X1 X2) X2) = (k X2 (M.op X1 X2)) ∨ (M.op X1 X2) = X2 ∨ (k X0 (M.op X1 X2)) = (M.op (M.op X1 X2) X0) ∨ (M.op X1 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42 X2 X1 (M.op X1 X2)
       have i₂ := eq14 X0 (M.op X1 X2)
       grind)
    | (have i₁ := eq42 X0 X1 X2
       have i₂ := eq14 (M.op X2 (M.op X1 X0)) X1
       grind)
    | exact superpose eq14 eq42
    | (have j0 := eq42 X2 X1 (M.op X1 X2)
       have j1 := eq14 X2 (M.op X1 X2)
       grind)
    | exact resolve eq42 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq218 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X2)) = (M.op (M.op X1 X2) X0) ∨ (M.op X1 X2) = (k X2 (M.op X1 X2)) ∨ (M.op X1 X2) = X2 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq207 X0 X1 X2
       have i₂ := eq33 X2 X1
       grind)
    | exact superpose eq33 eq207
    | (have j0 := eq207 X0 X1 X2
       grind)
    | exact resolve eq207 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq244 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 X2)) = (M.op (M.op (M.op X1 X2) (M.op X0 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X0 (M.op (M.op X1 X2) (M.op X0 X2))
       have i₂ := eq35 X2 X0 X1
       grind)
    | exact superpose eq35 eq31
    | exact resolve eq31 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq315 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ X0) (M.op X2 (σ (k X0 X1))))) = X2 ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X0) (σ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq9
    | (have j1 := eq38 X1 X0
       grind)
    | exact resolve eq9 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X1) (σ X0)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq31
    | (have j1 := eq38 X1 X0
       grind)
    | exact resolve eq31 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (M.op (σ X0) (σ X0)) (σ X2)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X2
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq15
    | (have j1 := eq38 X0 X1
       grind)
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1983 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (σ X0) = (k (σ X0) X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0
       have i₂ := eq55 X0 X1
       grind)
    | (have i₁ := eq53 X0
       have i₂ := eq55 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq55 eq53
    | (have j1 := eq55 X1 X0
       grind)
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq55
  have eq2347 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq144 y x
       grind)
    | exact superpose eq144 eq16
    | (have j1 := eq144 y x
       grind)
    | exact resolve eq16 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2352 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X1) (σ X0)
       have i₂ := eq144 X0 X1
       grind)
    | exact superpose eq144 eq31
    | (have j1 := eq144 X0 X1
       grind)
    | exact resolve eq31 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq3523 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq318 (τ X0) (τ X1)
       have i₂ := eq64 X1 X0
       grind)
    | exact superpose eq64 eq318
    | (have j0 := eq318 (τ X0) (τ X1)
       grind)
    | exact resolve eq318 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq3731 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3523 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq3523
    | (have j0 := eq3523 X0 X1
       grind)
    | exact resolve eq3523 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3523
  have eq3744 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3731 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3731
    | (have j0 := eq3731 X0 X1
       grind)
    | exact resolve eq3731 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3731
  have eq3747 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X0 (k X0 X1)) = X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3744 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3744
    | (have j0 := eq3744 X0 X1
       grind)
    | exact resolve eq3744 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3744
  have eq3748 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 (k X0 X1)) = X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3747 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3747
    | (have j0 := eq3747 X0 X1
       grind)
    | exact resolve eq3747 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3747
  have eq3749 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3748 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3748
    | (have j0 := eq3748 X0 X1
       grind)
    | exact resolve eq3748 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3748
  have eq3750 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3749 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3749
    | (have j0 := eq3749 X0 X1
       grind)
    | exact resolve eq3749 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3749
  have eq3826 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X1
       have i₂ := eq3750 X0 X1
       grind)
    | (have i₁ := eq31 X0 X1
       have i₂ := eq3750 (M.op X0 X1) X1
       grind)
    | exact superpose eq3750 eq31
    | (have j1 := eq3750 X0 X1
       grind)
    | exact resolve eq31 eq3750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3750
  have eq4218 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 (k X0 X2)))) = X1 ∨ (M.op X2 X0) = X2 ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35 (k X0 X2) X1 X0
       have i₂ := eq3826 X0 X2
       grind)
    | exact superpose eq3826 eq35
    | (have j1 := eq3826 X0 X2
       grind)
    | exact resolve eq35 eq3826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq3826
  have eq4578 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 X0)) (M.op X1 (σ (M.op X0 X0))))) = X1 ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    grind
  clear eq315
  have eq4865 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4578 X0 X1
       have i₂ := eq31 X1 (σ (M.op X0 X0))
       grind)
    | exact superpose eq31 eq4578
    | (have j0 := eq4578 X0 X1
       grind)
    | exact resolve eq4578 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4578
  have eq7900 : ∀ X0 X1 X2 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (k X1 X2)) = (k (M.op X0 X0) (σ X2)) ∨ (σ X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq324 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq324
    | exact resolve eq324 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq8096 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (M.op X0 X0) (σ X2)) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7900 X0 X1 X2
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq7900
    | (have j0 := eq7900 X0 X1 X2
       grind)
    | exact resolve eq7900 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq7900
  have eq21771 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) X0) ∨ (M.op X1 X0) = (k X0 (M.op X1 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq218 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq21772 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) X0) ∨ (M.op X1 X0) = (k X0 (M.op X1 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq21771 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21771
  have eq21871 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op X1 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq21772 X0 X1
       grind)
    | (have r₁ := eq21772 X0 X1
       have r₂ := eq33 X0 X1
       grind)
    | exact resolve eq21772 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq21772
  have eq48685 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1983 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1983
    | (have j0 := eq1983 X1 (σ X0)
       grind)
    | exact resolve eq1983 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1983
  have eq49011 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48685 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq48685
    | (have j0 := eq48685 X0 X1
       grind)
    | exact resolve eq48685 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48685
  have eq49030 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49011 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq49011
    | (have j0 := eq49011 X0 X1
       grind)
    | exact resolve eq49011 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49011
  have eq49265 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq49030 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49359 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq2347
       have i₂ := eq49030 x y
       grind)
    | exact superpose eq49030 eq2347
    | (have j1 := eq49030 x y
       grind)
    | (have r₁ := eq2347
       have r₂ := eq49030 x y
       grind)
    | (have r₁ := eq2347
       have r₂ := eq49030 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2347
       have r₂ := eq49030 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2347 eq49030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2347 eq49030
  have eq49364 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) ∨ x = y := by grind
  clear eq49359
  have eq49380 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq49265 y x
       grind)
    | (have r₁ := eq49364
       have r₂ := eq49265 y x
       grind)
    | exact resolve eq49364 eq49265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49265 eq49364
  have eq49419 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq49380
       grind)
    | exact superpose eq49380 eq10
    | exact resolve eq10 eq49380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49380
  have eq49574 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq49419
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq49419
    | exact resolve eq49419 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49419
  have eq49770 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq49574
       grind)
    | exact superpose eq49574 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq49574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49794 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 y))) = X0 ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq4218 y X0 x
       have i₂ := eq49574
       grind)
    | exact superpose eq49574 eq4218
    | (have j0 := eq4218 y x x
       grind)
    | exact resolve eq4218 eq49574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4218 eq49574
  have eq49831 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 y))) = X0 ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq49794 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49794
  have eq49855 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq49770
  have eq49869 : ∀ X0 : G, x = (M.op x y) ∨ (M.op X0 y) = X0 ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq49831 X0
       have i₂ := eq31 X0 y
       grind)
    | exact superpose eq31 eq49831
    | exact resolve eq49831 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49831
  have eq58548 : x = y ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq49869 x
       have i₂ := eq49855
       grind)
    | exact superpose eq49855 eq49869
    | exact resolve eq49869 eq49855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49855
  have eq58792 : x ≠ x ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have j0 := eq49869 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49869
  have eq58793 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq58792
  have eq58813 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq58548
  have eq61013 : y = (k x y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq21871 x x
       have i₂ := eq58813
       grind)
    | exact superpose eq58813 eq21871
    | exact resolve eq21871 eq58813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21871 eq58813
  have eq61014 : y = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq61013
  have eq63167 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2352 x y
       have i₂ := eq61014
       grind)
    | exact superpose eq61014 eq2352
    | (have j0 := eq2352 x y
       grind)
    | exact resolve eq2352 eq61014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2352 eq61014
  have eq63240 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq63167
  have eq66797 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq63240
       grind)
    | exact superpose eq63240 eq16
    | exact resolve eq16 eq63240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63240
  have eq67664 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq66797
       have i₂ := eq58793
       grind)
    | exact superpose eq58793 eq66797
    | exact resolve eq66797 eq58793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58793 eq66797
  have eq67679 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq67664
  have eq67680 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq67679
  have eq68311 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq67680
       grind)
    | exact superpose eq67680 eq10
    | exact resolve eq10 eq67680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67680
  have eq68429 : x = y ∨ x = y := by
    first
    | (have i₁ := eq68311
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq68311
    | exact resolve eq68311 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68311
  have eq68430 : x = y := by grind
  clear eq68429
  have eq68888 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq68430
       grind)
    | exact superpose eq68430 eq16
    | exact resolve eq16 eq68430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68430
  have eq69365 : ∀ X0 : G, (σ (M.op x x)) ≠ X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = X0 := by
    intro X0
    first
    | (have i₁ := eq68888
       have i₂ := eq14 X0 (σ x)
       grind)
    | (have i₁ := eq68888
       have i₂ := eq14 (M.op (σ x) (σ x)) x
       grind)
    | exact superpose eq14 eq68888
    | (have j1 := eq14 X0 (σ x)
       grind)
    | (have r₁ := eq68888
       have r₂ := eq14 (σ (M.op x x)) (σ x)
       grind)
    | (have r₁ := eq68888
       have r₂ := eq14 (M.op (σ x) (σ x)) (σ (M.op x x))
       grind)
    | (have r₁ := eq68888
       have r₂ := eq14 (σ (M.op x x)) (M.op (σ x) (σ x))
       grind)
    | exact resolve eq68888 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73724 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (M.op X2 X2) (σ (τ X1))) ∨ (k (σ (τ X0)) X2) = (M.op X2 (σ (τ X0))) ∨ (σ (τ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8096 X2 (τ X0) (τ X1)
       have i₂ := eq64 X1 X0
       grind)
    | exact superpose eq64 eq8096
    | (have j0 := eq8096 X2 (τ X0) X2
       grind)
    | exact resolve eq8096 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq8096
  have eq74535 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (M.op X2 X2) X1) ∨ (k (σ (τ X0)) X2) = (M.op X2 (σ (τ X0))) ∨ (σ (τ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq73724 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq73724
    | (have j0 := eq73724 X0 X1 X2
       grind)
    | exact resolve eq73724 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73724
  have eq74587 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (M.op X2 X2) X1) ∨ (k (σ (τ X0)) X2) = (M.op X2 (σ (τ X0))) ∨ (σ (τ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74535 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq74535
    | (have j0 := eq74535 X0 X1 X2
       grind)
    | exact resolve eq74535 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74535
  have eq74614 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X0 X2) ∨ (k X0 X1) = (k (M.op X2 X2) X1) ∨ (σ (τ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74587 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq74587
    | (have j0 := eq74587 X0 X1 X2
       grind)
    | exact resolve eq74587 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74587
  have eq74624 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (M.op X2 X2) X1) ∨ (M.op X2 X0) = (k X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74614 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq74614
    | (have j0 := eq74614 X0 X1 X2
       grind)
    | exact resolve eq74614 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74614
  have eq99520 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq74624 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74624
  have eq99566 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  clear eq99520
  have eq135424 : (k (σ (M.op x x)) (σ x)) = (M.op (σ x) (σ (M.op x x))) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have j0 := eq69365 (σ (M.op x x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69365
  have eq135425 : (M.op (σ x) (σ (M.op x x))) = (σ (k (M.op x x) x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq135424
       have i₂ := eq15 (M.op x x) x
       grind)
    | exact superpose eq15 eq135424
    | exact resolve eq135424 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135424
  have eq135426 : (σ (M.op x x)) = (M.op (σ x) (σ (M.op x x))) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq135425
  have eq135498 : (σ x) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4865 x (σ x)
       have i₂ := eq135426
       grind)
    | exact superpose eq135426 eq4865
    | (have j0 := eq4865 x x
       grind)
    | exact resolve eq4865 eq135426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4865 eq135426
  have eq135530 : (σ x) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq135498
  have eq135561 : (σ x) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq135530
       have r₂ := eq68888
       grind)
    | exact resolve eq135530 eq68888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135530
  have eq135616 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq135561
       grind)
    | exact superpose eq135561 eq10
    | exact resolve eq10 eq135561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135788 : x = (M.op x x) := by
    first
    | (have i₁ := eq135616
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq135616
    | exact resolve eq135616 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135616
  have eq135932 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op (M.op x (M.op X0 x)) X0) := by
    intro X0
    first
    | (have i₁ := eq244 X0 x x
       have i₂ := eq135788
       grind)
    | exact superpose eq135788 eq244
    | exact resolve eq244 eq135788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq136054 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq135932 X0
       have i₂ := eq31 X0 x
       grind)
    | exact superpose eq31 eq135932
    | exact resolve eq135932 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq135932
  have eq136353 : ∀ X0 : G, x ≠ (M.op x x) ∨ x = (k X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq99566 X0 x
       have i₂ := eq136054 X0
       grind)
    | exact superpose eq136054 eq99566
    | (have j0 := eq99566 x (k X0 x)
       grind)
    | exact resolve eq99566 eq136054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99566 eq136054
  have eq136560 : ∀ X0 : G, x = (k X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq136353 X0
       grind)
    | (have r₁ := eq136353 X0
       have r₂ := eq135788
       grind)
    | exact resolve eq136353 eq135788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135788 eq136353
  have eq137288 : x = (τ (M.op (σ x) (σ x))) ∨ x = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq67 x
       have i₂ := eq136560 (τ (M.op (σ x) (σ x)))
       grind)
    | exact superpose eq136560 eq67
    | (have j1 := eq136560 (τ (M.op (σ x) (σ x)))
       grind)
    | exact resolve eq67 eq136560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq136560
  have eq137324 : x = (τ (M.op (σ x) (σ x))) := by grind
  clear eq137288
  have eq137609 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ x))
       have i₂ := eq137324
       grind)
    | exact superpose eq137324 eq11
    | exact resolve eq11 eq137324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137324
  have eq138423 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq68888
       have i₂ := eq137609
       grind)
    | exact superpose eq137609 eq68888
    | exact resolve eq68888 eq137609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68888 eq137609
  have eq138706 : False := by grind
  exact eq138706

/-- `Equation433`: `x = x ◇ (y ◇ (x ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then X else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_x_x_pyx_Equation433 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law433 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law433.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
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
  have eq27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq31 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (M.op X1 X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq31
    | exact resolve eq31 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X2 X0) X0
       have i₂ := eq31 X2 X0
       grind)
    | exact superpose eq31 eq9
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq40 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq42 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X1 X0))) = X1 ∨ (M.op X2 X0) = (k X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 X2
       have i₂ := eq14 X0 X2
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 (M.op X2 X1) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X2
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  have eq55 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = X1 := by
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
  have eq64 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27
    | exact resolve eq27 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  clear eq27
  have eq144 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq40 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq40
    | (have j0 := eq40 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq40 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq207 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (M.op (M.op X1 X2) X2) = (k X2 (M.op X1 X2)) ∨ (M.op X1 X2) = X2 ∨ (k X0 (M.op X1 X2)) = (M.op (M.op X1 X2) X0) ∨ (M.op X1 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42 X2 X1 (M.op X1 X2)
       have i₂ := eq14 X0 (M.op X1 X2)
       grind)
    | (have i₁ := eq42 X0 X1 X2
       have i₂ := eq14 (M.op X2 (M.op X1 X0)) X1
       grind)
    | exact superpose eq14 eq42
    | (have j0 := eq42 X2 X1 (M.op X1 X2)
       have j1 := eq14 X2 (M.op X1 X2)
       grind)
    | exact resolve eq42 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq218 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X2)) = (M.op (M.op X1 X2) X0) ∨ (M.op X1 X2) = (k X2 (M.op X1 X2)) ∨ (M.op X1 X2) = X2 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq207 X0 X1 X2
       have i₂ := eq33 X2 X1
       grind)
    | exact superpose eq33 eq207
    | (have j0 := eq207 X0 X1 X2
       grind)
    | exact resolve eq207 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq244 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 X2)) = (M.op (M.op (M.op X1 X2) (M.op X0 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X0 (M.op (M.op X1 X2) (M.op X0 X2))
       have i₂ := eq35 X2 X0 X1
       grind)
    | exact superpose eq35 eq31
    | exact resolve eq31 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq315 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ X0) (M.op X2 (σ (k X0 X1))))) = X2 ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X0) (σ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq9
    | (have j1 := eq38 X1 X0
       grind)
    | exact resolve eq9 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X1) (σ X0)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq31
    | (have j1 := eq38 X1 X0
       grind)
    | exact resolve eq31 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (M.op (σ X0) (σ X0)) (σ X2)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X2
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq15
    | (have j1 := eq38 X0 X1
       grind)
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1983 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (σ X0) = (k (σ X0) X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0
       have i₂ := eq55 X0 X1
       grind)
    | (have i₁ := eq53 X0
       have i₂ := eq55 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq55 eq53
    | (have j1 := eq55 X1 X0
       grind)
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq55
  have eq2347 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq144 y x
       grind)
    | exact superpose eq144 eq16
    | (have j1 := eq144 y x
       grind)
    | exact resolve eq16 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2352 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X1) (σ X0)
       have i₂ := eq144 X0 X1
       grind)
    | exact superpose eq144 eq31
    | (have j1 := eq144 X0 X1
       grind)
    | exact resolve eq31 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq3523 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq318 (τ X0) (τ X1)
       have i₂ := eq64 X1 X0
       grind)
    | exact superpose eq64 eq318
    | (have j0 := eq318 (τ X0) (τ X1)
       grind)
    | exact resolve eq318 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq3731 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3523 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq3523
    | (have j0 := eq3523 X0 X1
       grind)
    | exact resolve eq3523 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3523
  have eq3744 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3731 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3731
    | (have j0 := eq3731 X0 X1
       grind)
    | exact resolve eq3731 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3731
  have eq3747 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X0 (k X0 X1)) = X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3744 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3744
    | (have j0 := eq3744 X0 X1
       grind)
    | exact resolve eq3744 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3744
  have eq3748 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 (k X0 X1)) = X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3747 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3747
    | (have j0 := eq3747 X0 X1
       grind)
    | exact resolve eq3747 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3747
  have eq3749 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3748 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3748
    | (have j0 := eq3748 X0 X1
       grind)
    | exact resolve eq3748 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3748
  have eq3750 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3749 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3749
    | (have j0 := eq3749 X0 X1
       grind)
    | exact resolve eq3749 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3749
  have eq3826 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X1
       have i₂ := eq3750 X0 X1
       grind)
    | (have i₁ := eq31 X0 X1
       have i₂ := eq3750 (M.op X0 X1) X1
       grind)
    | exact superpose eq3750 eq31
    | (have j1 := eq3750 X0 X1
       grind)
    | exact resolve eq31 eq3750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3750
  have eq4218 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 (k X0 X2)))) = X1 ∨ (M.op X2 X0) = X2 ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35 (k X0 X2) X1 X0
       have i₂ := eq3826 X0 X2
       grind)
    | exact superpose eq3826 eq35
    | (have j1 := eq3826 X0 X2
       grind)
    | exact resolve eq35 eq3826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq3826
  have eq4578 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 X0)) (M.op X1 (σ (M.op X0 X0))))) = X1 ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    grind
  clear eq315
  have eq4865 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4578 X0 X1
       have i₂ := eq31 X1 (σ (M.op X0 X0))
       grind)
    | exact superpose eq31 eq4578
    | (have j0 := eq4578 X0 X1
       grind)
    | exact resolve eq4578 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4578
  have eq7900 : ∀ X0 X1 X2 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (k X1 X2)) = (k (M.op X0 X0) (σ X2)) ∨ (σ X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq324 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq324
    | exact resolve eq324 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq8096 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (M.op X0 X0) (σ X2)) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7900 X0 X1 X2
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq7900
    | (have j0 := eq7900 X0 X1 X2
       grind)
    | exact resolve eq7900 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq7900
  have eq21771 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) X0) ∨ (M.op X1 X0) = (k X0 (M.op X1 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq218 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq21772 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) X0) ∨ (M.op X1 X0) = (k X0 (M.op X1 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq21771 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21771
  have eq21871 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op X1 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq21772 X0 X1
       grind)
    | (have r₁ := eq21772 X0 X1
       have r₂ := eq33 X0 X1
       grind)
    | exact resolve eq21772 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq21772
  have eq48685 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1983 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1983
    | (have j0 := eq1983 X1 (σ X0)
       grind)
    | exact resolve eq1983 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1983
  have eq49011 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48685 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq48685
    | (have j0 := eq48685 X0 X1
       grind)
    | exact resolve eq48685 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48685
  have eq49030 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49011 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq49011
    | (have j0 := eq49011 X0 X1
       grind)
    | exact resolve eq49011 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49011
  have eq49265 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq49030 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49359 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq2347
       have i₂ := eq49030 x y
       grind)
    | exact superpose eq49030 eq2347
    | (have j1 := eq49030 x y
       grind)
    | (have r₁ := eq2347
       have r₂ := eq49030 x y
       grind)
    | (have r₁ := eq2347
       have r₂ := eq49030 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2347
       have r₂ := eq49030 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2347 eq49030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2347 eq49030
  have eq49364 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) ∨ x = y := by grind
  clear eq49359
  have eq49380 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq49265 y x
       grind)
    | (have r₁ := eq49364
       have r₂ := eq49265 y x
       grind)
    | exact resolve eq49364 eq49265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49265 eq49364
  have eq49419 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq49380
       grind)
    | exact superpose eq49380 eq10
    | exact resolve eq10 eq49380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49380
  have eq49574 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq49419
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq49419
    | exact resolve eq49419 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49419
  have eq49770 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq49574
       grind)
    | exact superpose eq49574 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq49574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49794 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 y))) = X0 ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq4218 y X0 x
       have i₂ := eq49574
       grind)
    | exact superpose eq49574 eq4218
    | (have j0 := eq4218 y x x
       grind)
    | exact resolve eq4218 eq49574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4218 eq49574
  have eq49831 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 y))) = X0 ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq49794 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49794
  have eq49855 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq49770
  have eq49869 : ∀ X0 : G, x = (M.op x y) ∨ (M.op X0 y) = X0 ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq49831 X0
       have i₂ := eq31 X0 y
       grind)
    | exact superpose eq31 eq49831
    | exact resolve eq49831 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49831
  have eq58548 : x = y ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq49869 x
       have i₂ := eq49855
       grind)
    | exact superpose eq49855 eq49869
    | exact resolve eq49869 eq49855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49855
  have eq58792 : x ≠ x ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have j0 := eq49869 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49869
  have eq58793 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq58792
  have eq58813 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq58548
  have eq61013 : y = (k x y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq21871 x x
       have i₂ := eq58813
       grind)
    | exact superpose eq58813 eq21871
    | exact resolve eq21871 eq58813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21871 eq58813
  have eq61014 : y = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq61013
  have eq63167 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2352 x y
       have i₂ := eq61014
       grind)
    | exact superpose eq61014 eq2352
    | (have j0 := eq2352 x y
       grind)
    | exact resolve eq2352 eq61014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2352 eq61014
  have eq63240 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq63167
  have eq66797 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq63240
       grind)
    | exact superpose eq63240 eq16
    | exact resolve eq16 eq63240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63240
  have eq67664 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq66797
       have i₂ := eq58793
       grind)
    | exact superpose eq58793 eq66797
    | exact resolve eq66797 eq58793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58793 eq66797
  have eq67679 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq67664
  have eq67680 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq67679
  have eq68311 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq67680
       grind)
    | exact superpose eq67680 eq10
    | exact resolve eq10 eq67680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67680
  have eq68429 : x = y ∨ x = y := by
    first
    | (have i₁ := eq68311
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq68311
    | exact resolve eq68311 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68311
  have eq68430 : x = y := by grind
  clear eq68429
  have eq68888 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq68430
       grind)
    | exact superpose eq68430 eq16
    | exact resolve eq16 eq68430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68430
  have eq69365 : ∀ X0 : G, (σ (M.op x x)) ≠ X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = X0 := by
    intro X0
    first
    | (have i₁ := eq68888
       have i₂ := eq14 X0 (σ x)
       grind)
    | (have i₁ := eq68888
       have i₂ := eq14 (M.op (σ x) (σ x)) x
       grind)
    | exact superpose eq14 eq68888
    | (have j1 := eq14 X0 (σ x)
       grind)
    | (have r₁ := eq68888
       have r₂ := eq14 (σ (M.op x x)) (σ x)
       grind)
    | (have r₁ := eq68888
       have r₂ := eq14 (M.op (σ x) (σ x)) (σ (M.op x x))
       grind)
    | (have r₁ := eq68888
       have r₂ := eq14 (σ (M.op x x)) (M.op (σ x) (σ x))
       grind)
    | exact resolve eq68888 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73724 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (M.op X2 X2) (σ (τ X1))) ∨ (k (σ (τ X0)) X2) = (M.op X2 (σ (τ X0))) ∨ (σ (τ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8096 X2 (τ X0) (τ X1)
       have i₂ := eq64 X1 X0
       grind)
    | exact superpose eq64 eq8096
    | (have j0 := eq8096 X2 (τ X0) X2
       grind)
    | exact resolve eq8096 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq8096
  have eq74535 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (M.op X2 X2) X1) ∨ (k (σ (τ X0)) X2) = (M.op X2 (σ (τ X0))) ∨ (σ (τ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq73724 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq73724
    | (have j0 := eq73724 X0 X1 X2
       grind)
    | exact resolve eq73724 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73724
  have eq74587 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (M.op X2 X2) X1) ∨ (k (σ (τ X0)) X2) = (M.op X2 (σ (τ X0))) ∨ (σ (τ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74535 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq74535
    | (have j0 := eq74535 X0 X1 X2
       grind)
    | exact resolve eq74535 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74535
  have eq74614 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X0 X2) ∨ (k X0 X1) = (k (M.op X2 X2) X1) ∨ (σ (τ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74587 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq74587
    | (have j0 := eq74587 X0 X1 X2
       grind)
    | exact resolve eq74587 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74587
  have eq74624 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (M.op X2 X2) X1) ∨ (M.op X2 X0) = (k X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74614 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq74614
    | (have j0 := eq74614 X0 X1 X2
       grind)
    | exact resolve eq74614 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74614
  have eq99520 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq74624 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74624
  have eq99566 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  clear eq99520
  have eq114164 : (k (σ (M.op x x)) (σ x)) = (M.op (σ x) (σ (M.op x x))) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have j0 := eq69365 (σ (M.op x x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69365
  have eq114165 : (M.op (σ x) (σ (M.op x x))) = (σ (k (M.op x x) x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq114164
       have i₂ := eq15 (M.op x x) x
       grind)
    | exact superpose eq15 eq114164
    | exact resolve eq114164 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114164
  have eq114166 : (σ (M.op x x)) = (M.op (σ x) (σ (M.op x x))) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq114165
  have eq114206 : (σ x) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4865 x (σ x)
       have i₂ := eq114166
       grind)
    | exact superpose eq114166 eq4865
    | (have j0 := eq4865 x x
       grind)
    | exact resolve eq4865 eq114166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4865 eq114166
  have eq114238 : (σ x) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq114206
  have eq114269 : (σ x) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq114238
       have r₂ := eq68888
       grind)
    | exact resolve eq114238 eq68888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114238
  have eq114350 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq114269
       grind)
    | exact superpose eq114269 eq10
    | exact resolve eq10 eq114269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114522 : x = (M.op x x) := by
    first
    | (have i₁ := eq114350
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq114350
    | exact resolve eq114350 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114350
  have eq114662 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op (M.op x (M.op X0 x)) X0) := by
    intro X0
    first
    | (have i₁ := eq244 X0 x x
       have i₂ := eq114522
       grind)
    | exact superpose eq114522 eq244
    | exact resolve eq244 eq114522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq114782 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq114662 X0
       have i₂ := eq31 X0 x
       grind)
    | exact superpose eq31 eq114662
    | exact resolve eq114662 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq114662
  have eq115036 : ∀ X0 : G, x ≠ (M.op x x) ∨ x = (k X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq99566 X0 x
       have i₂ := eq114782 X0
       grind)
    | exact superpose eq114782 eq99566
    | (have j0 := eq99566 x (k X0 x)
       grind)
    | exact resolve eq99566 eq114782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99566 eq114782
  have eq115237 : ∀ X0 : G, x = (k X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq115036 X0
       grind)
    | (have r₁ := eq115036 X0
       have r₂ := eq114522
       grind)
    | exact resolve eq115036 eq114522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114522 eq115036
  have eq115973 : x = (τ (M.op (σ x) (σ x))) ∨ x = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq67 x
       have i₂ := eq115237 (τ (M.op (σ x) (σ x)))
       grind)
    | exact superpose eq115237 eq67
    | (have j1 := eq115237 (τ (M.op (σ x) (σ x)))
       grind)
    | exact resolve eq67 eq115237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq115237
  have eq116009 : x = (τ (M.op (σ x) (σ x))) := by grind
  clear eq115973
  have eq116285 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ x))
       have i₂ := eq116009
       grind)
    | exact superpose eq116009 eq11
    | exact resolve eq11 eq116009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116009
  have eq117047 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq68888
       have i₂ := eq116285
       grind)
    | exact superpose eq116285 eq68888
    | exact resolve eq68888 eq116285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68888 eq116285
  have eq117325 : False := by grind
  exact eq117325

/-- `Equation4343`: `x ◇ (y ◇ y) = y ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_pxx_pxy_Equation4343 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4343 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4343.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq53 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq59 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq71 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq53 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq77 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq69 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq69 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq69 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq108 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq77 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq109 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq108 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq113 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq109 (σ X0)
       grind)
    | exact superpose eq109 eq15
    | exact resolve eq15 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq113 X0
       have i₂ := eq109 X0
       grind)
    | exact superpose eq109 eq113
    | exact resolve eq113 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq113
  have eq165 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 X1)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq124 X0
       grind)
    | exact superpose eq124 eq9
    | exact resolve eq9 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq124 X0
       grind)
    | exact superpose eq124 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq124 X0
       grind)
    | exact superpose eq124 eq14
    | (have j0 := eq14 X1 X1
       grind)
    | exact resolve eq14 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq169 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq169 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq169 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq202 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq203 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq202 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq310 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq203 (τ X0) X1
       grind)
    | exact superpose eq203 eq17
    | (have j1 := eq203 X0 X1
       grind)
    | exact resolve eq17 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq203
  have eq362 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X1 X1))) = (M.op (σ X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq165 X0 (σ X1)
       have i₂ := eq124 X1
       grind)
    | exact superpose eq124 eq165
    | exact resolve eq165 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq165
  have eq2488 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq310 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq310
    | (have j0 := eq310 X0 X1
       grind)
    | exact resolve eq310 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq2613 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2488 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2488
    | (have j0 := eq2488 X0 X1
       grind)
    | exact resolve eq2488 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2488
  have eq6588 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq171 X0 X1
       grind)
    | exact superpose eq171 eq10
    | (have j1 := eq171 X0 X1
       grind)
    | exact resolve eq10 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq6677 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6588 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6588
    | (have j0 := eq6588 X0 X1
       grind)
    | exact resolve eq6588 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6588
  have eq7418 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq6677 X1 (σ X0)
       grind)
    | exact superpose eq6677 eq15
    | (have j1 := eq6677 X1 X1
       grind)
    | exact resolve eq15 eq6677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6677
  have eq9323 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7418 x y
       grind)
    | exact superpose eq7418 eq16
    | (have j1 := eq7418 x y
       grind)
    | exact resolve eq16 eq7418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7418
  have eq9517 : y = (M.op y y) := by
    first
    | (have j1 := eq2613 x y
       grind)
    | (have r₁ := eq9323
       have r₂ := eq2613 x y
       grind)
    | exact resolve eq9323 eq2613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2613 eq9323
  have eq9844 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq9 y X0
       have i₂ := eq9517
       grind)
    | exact superpose eq9517 eq9
    | exact resolve eq9 eq9517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9845 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq9517
       grind)
    | exact superpose eq9517 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq9517
       grind)
    | exact resolve eq12 eq9517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9857 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq166 y X0
       have i₂ := eq9517
       grind)
    | exact superpose eq9517 eq166
    | (have j0 := eq166 y X0
       grind)
    | exact resolve eq166 eq9517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq9875 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq9857 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9857
  have eq9877 : ∀ X0 : G, (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq9845 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9845
  have eq10743 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq9875 (σ X0)
       grind)
    | exact superpose eq9875 eq15
    | exact resolve eq15 eq9875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9875
  have eq10788 : ∀ X0 : G, (σ (M.op y X0)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10743 X0
       have i₂ := eq9877 X0
       grind)
    | exact superpose eq9877 eq10743
    | exact resolve eq10743 eq9877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9877 eq10743
  have eq13167 : ∀ X0 : G, (M.op (σ X0) (σ (M.op y y))) = (σ (M.op y (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq362 y X0
       have i₂ := eq10788 (M.op X0 X0)
       grind)
    | exact superpose eq10788 eq362
    | exact resolve eq362 eq10788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362 eq10788
  have eq13248 : ∀ X0 : G, (M.op (σ X0) (σ (M.op y y))) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq13167 X0
       have i₂ := eq9844 X0
       grind)
    | exact superpose eq9844 eq13167
    | exact resolve eq13167 eq9844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9844 eq13167
  have eq13279 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq13248 X0
       have i₂ := eq9517
       grind)
    | exact superpose eq9517 eq13248
    | exact resolve eq13248 eq9517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9517 eq13248
  have eq15340 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13279 x
       grind)
    | exact superpose eq13279 eq16
    | (have r₁ := eq16
       have r₂ := eq13279 x
       grind)
    | exact resolve eq16 eq13279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13279
  have eq15418 : False := by grind
  exact eq15418
