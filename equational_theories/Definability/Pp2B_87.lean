import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxy_pyx_Equation838 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law838 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq83 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq83 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq83 X0 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq296 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq279 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq297 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq296 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq301 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq297 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq297
    | (have j0 := eq297 X0 X1
       grind)
    | exact resolve eq297 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq302 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq301 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq540 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq302 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq302
    | exact resolve eq302 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq302 x y
       grind)
    | exact superpose eq302 eq16
    | (have j1 := eq302 x y
       grind)
    | exact resolve eq16 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq572 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq540 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq540
    | (have j0 := eq540 X0 X1
       grind)
    | exact resolve eq540 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq540
  have eq573 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq572 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq572
    | exact resolve eq572 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq632 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq573 (τ X1) X0
       grind)
    | exact superpose eq573 eq18
    | (have j1 := eq573 (τ X1) X0
       grind)
    | exact resolve eq18 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq573
  have eq877 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq632 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq632
    | exact resolve eq632 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq928 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq877 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq877
    | (have j0 := eq877 X0 X1
       grind)
    | exact resolve eq877 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877
  have eq1013 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq554
       have i₂ := eq928 y x
       grind)
    | exact superpose eq928 eq554
    | (have j1 := eq928 (σ y) (σ x)
       grind)
    | (have r₁ := eq554
       have r₂ := eq928 y x
       grind)
    | exact resolve eq554 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1014 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1013
  have eq1018 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1014
  have eq1070 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq554
       have i₂ := eq1018
       grind)
    | exact superpose eq1018 eq554
    | exact resolve eq554 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554 eq1018
  have eq1071 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1070
  have eq1072 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1071
  have eq1082 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1072
  have eq1097 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1082
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1082
    | exact resolve eq1082 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082
  have eq1143 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1097
       grind)
    | exact superpose eq1097 eq16
    | exact resolve eq16 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097
  have eq1159 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1143
       have i₂ := eq928 y x
       grind)
    | exact superpose eq928 eq1143
    | (have j1 := eq928 y x
       grind)
    | (have r₁ := eq1143
       have r₂ := eq928 y x
       grind)
    | exact resolve eq1143 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq1160 : y = (M.op x x) := by grind
  clear eq1159
  have eq1209 : (M.op x y) = (k y x) := by grind
  clear eq1160
  have eq1222 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1143
       have i₂ := eq1209
       grind)
    | exact superpose eq1209 eq1143
    | exact resolve eq1143 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143 eq1209
  have eq1225 : False := by grind
  exact eq1225

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pxy_pyx_pxy_Equation838 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law838 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
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
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op (M.op (M.op X1 X0) (M.op X2 X0)) (M.op (M.op X3 (M.op (M.op X1 X0) (M.op X2 X0))) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X2 X0)) X3 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21
    | exact resolve eq21 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq53 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq34
    | exact resolve eq34 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq72 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq72 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq72 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq72 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq75 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq53 X0 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq53
    | exact resolve eq53 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq77 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq15
    | exact resolve eq15 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq77 X0
       have i₂ := eq73 (σ X0)
       grind)
    | exact superpose eq73 eq77
    | exact resolve eq77 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq79 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq76 X0
       have i₂ := eq73 (τ X0)
       grind)
    | exact superpose eq73 eq76
    | exact resolve eq76 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq76
  have eq89 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq75 x y
       grind)
    | exact superpose eq75 eq16
    | (have j1 := eq75 x y
       grind)
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq103 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op y y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq89
       have i₂ := eq14 (σ x) (σ y)
       grind)
    | exact superpose eq14 eq89
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq89
       have r₂ := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq89 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq104 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq103
  have eq731 : (τ (M.op (σ x) (σ x))) = (M.op (τ (σ y)) (τ (σ y))) ∨ y = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq79 (σ y)
       have i₂ := eq104
       grind)
    | exact superpose eq104 eq79
    | exact resolve eq79 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq750 : (M.op y y) = (τ (M.op (σ x) (σ x))) ∨ y = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq731
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq731
    | exact resolve eq731 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq772 : (M.op y y) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq750
       have i₂ := eq79 (σ x)
       grind)
    | exact superpose eq79 eq750
    | exact resolve eq750 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq775 : (M.op y y) = (M.op x x) ∨ y = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq772
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq772
    | exact resolve eq772 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq776 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq775
  have eq801 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ y = (M.op y y) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq79 (σ y)
       have i₂ := eq776
       grind)
    | exact superpose eq776 eq79
    | exact resolve eq79 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq815 : y = (M.op y y) ∨ y = (M.op y y) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq801
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq801
    | exact resolve eq801 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq816 : (M.op y y) = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq815
  have eq849 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq78 y
       have i₂ := eq816
       grind)
    | exact superpose eq816 eq78
    | exact resolve eq78 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq864 : y = (M.op y y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq849
       have i₂ := eq78 x
       grind)
    | exact superpose eq78 eq849
    | exact resolve eq849 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq1040 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq864
       grind)
    | exact superpose eq864 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq864
       grind)
    | exact resolve eq12 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1043 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq78 y
       have i₂ := eq864
       grind)
    | exact superpose eq864 eq78
    | exact resolve eq78 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864
  have eq1067 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq1040 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040
  have eq1169 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (M.op X0 y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq1067 X0
       grind)
    | exact superpose eq1067 eq15
    | exact resolve eq15 eq1067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067
  have eq1209 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ y)
       have i₂ := eq1043
       grind)
    | exact superpose eq1043 eq12
    | (have j0 := eq12 X0 (σ y)
       grind)
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq1043
       grind)
    | exact resolve eq12 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043
  have eq1238 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq1209 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq1671 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1169 x
       grind)
    | exact superpose eq1169 eq16
    | exact resolve eq16 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169
  have eq1677 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq1671
       have r₂ := eq1238 (σ x)
       grind)
    | exact resolve eq1671 eq1238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238 eq1671
  have eq1708 : ∀ X0 : G, (M.op X0 (σ y)) = (k (σ y) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) ≠ (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq13 (σ y) X0
       have i₂ := eq1677
       grind)
    | exact superpose eq1677 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1677
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1677
       grind)
    | exact resolve eq13 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1710 : (τ (M.op (σ x) (σ x))) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq79 (σ y)
       have i₂ := eq1677
       grind)
    | exact superpose eq1677 eq79
    | exact resolve eq79 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1716 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ x)) (M.op X0 (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) (σ y) X0
       have i₂ := eq1677
       grind)
    | exact superpose eq1677 eq9
    | exact resolve eq9 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1740 : (M.op y y) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq1710
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1710
    | exact resolve eq1710 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1710
  have eq1743 : (M.op y y) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq1740
       have i₂ := eq79 (σ x)
       grind)
    | exact superpose eq79 eq1740
    | exact resolve eq1740 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1740
  have eq1745 : (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq1743
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1743
    | exact resolve eq1743 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743
  have eq1981 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq1745
       grind)
    | exact superpose eq1745 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1745
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1745
       grind)
    | exact resolve eq13 eq1745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1988 : ∀ X0 : G, y = (M.op y (M.op (M.op x x) (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq9 y y X0
       have i₂ := eq1745
       grind)
    | exact superpose eq1745 eq9
    | exact resolve eq9 eq1745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2022 : y = (M.op y (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq1988 y
       have i₂ := eq1745
       grind)
    | exact superpose eq1745 eq1988
    | exact resolve eq1988 eq1745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1988
  have eq2115 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op (M.op x x) (M.op x x)) (M.op y x)) := by
    first
    | (have i₁ := eq25 x x x y
       have i₂ := eq2022
       grind)
    | exact superpose eq2022 eq25
    | exact resolve eq25 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2275 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq1716 (σ y)
       have i₂ := eq1677
       grind)
    | exact superpose eq1677 eq1716
    | exact resolve eq1716 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1716
  have eq2421 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq25 (σ x) (σ x) (σ x) (σ y)
       have i₂ := eq2275
       grind)
    | exact superpose eq2275 eq25
    | exact resolve eq25 eq2275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq2541 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have j0 := eq1981 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1981
  have eq2554 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq15 y x
       have i₂ := eq2541
       grind)
    | exact superpose eq2541 eq15
    | exact resolve eq15 eq2541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2541
  have eq2564 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2554
       grind)
    | exact superpose eq2554 eq16
    | exact resolve eq16 eq2554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2554
  have eq3504 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2564
       have i₂ := eq1708 (σ x)
       grind)
    | exact superpose eq1708 eq2564
    | (have j1 := eq1708 (σ x)
       grind)
    | (have r₁ := eq2564
       have r₂ := eq1708 (σ x)
       grind)
    | exact resolve eq2564 eq1708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1708 eq2564
  have eq3509 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq3504
  have eq3521 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq79 (σ x)
       have i₂ := eq3509
       grind)
    | exact superpose eq3509 eq79
    | exact resolve eq79 eq3509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq3509
  have eq3566 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3521
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3521
    | exact resolve eq3521 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3521
  have eq3567 : x = (M.op x x) := by grind
  clear eq3566
  have eq3583 : x = (M.op y y) := by
    first
    | (have i₁ := eq1745
       have i₂ := eq3567
       grind)
    | exact superpose eq3567 eq1745
    | exact resolve eq1745 eq3567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1745
  have eq3633 : y = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq2022
       have i₂ := eq3567
       grind)
    | exact superpose eq3567 eq2022
    | exact resolve eq2022 eq3567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2022
  have eq3675 : (M.op x x) = (M.op (M.op x x) (M.op y x)) := by
    first
    | (have i₁ := eq2115
       have i₂ := eq3567
       grind)
    | exact superpose eq3567 eq2115
    | exact resolve eq2115 eq3567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2115
  have eq4251 : x = (M.op x (M.op y x)) := by
    first
    | (have i₁ := eq3675
       have i₂ := eq3567
       grind)
    | exact superpose eq3567 eq3675
    | exact resolve eq3675 eq3567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3675
  have eq4272 : y = (M.op y x) := by
    first
    | (have i₁ := eq3633
       have i₂ := eq3567
       grind)
    | exact superpose eq3567 eq3633
    | exact resolve eq3633 eq3567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3567 eq3633
  have eq4478 : x = (M.op x y) := by
    first
    | (have i₁ := eq4251
       have i₂ := eq4272
       grind)
    | exact superpose eq4272 eq4251
    | exact resolve eq4251 eq4272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4251 eq4272
  have eq4516 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4478
       grind)
    | exact superpose eq4478 eq16
    | exact resolve eq16 eq4478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4478
  have eq4732 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq78 y
       have i₂ := eq3583
       grind)
    | exact superpose eq3583 eq78
    | exact resolve eq78 eq3583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq3583
  have eq4759 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1677
       have i₂ := eq4732
       grind)
    | exact superpose eq4732 eq1677
    | exact resolve eq1677 eq4732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1677 eq4732
  have eq4894 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq2275
       have i₂ := eq4759
       grind)
    | exact superpose eq4759 eq2275
    | exact resolve eq2275 eq4759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2275
  have eq4939 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq2421
       have i₂ := eq4759
       grind)
    | exact superpose eq4759 eq2421
    | exact resolve eq2421 eq4759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2421
  have eq5075 : (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq4939
       have i₂ := eq4759
       grind)
    | exact superpose eq4759 eq4939
    | exact resolve eq4939 eq4759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4939
  have eq5114 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq4894
       have i₂ := eq4759
       grind)
    | exact superpose eq4759 eq4894
    | exact resolve eq4894 eq4759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4759 eq4894
  have eq5169 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5075
       have i₂ := eq5114
       grind)
    | exact superpose eq5114 eq5075
    | exact resolve eq5075 eq5114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5075 eq5114
  have eq5195 : False := by grind
  exact eq5195

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_y_pxy_Equation838 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law838 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq269 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq269 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq272 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq270 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq270 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq270 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq283 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq272 (σ X0)
       grind)
    | exact superpose eq272 eq15
    | exact resolve eq15 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq283 X0
       have i₂ := eq272 X0
       grind)
    | exact superpose eq272 eq283
    | exact resolve eq283 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq346 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq302 X0
       grind)
    | exact superpose eq302 eq9
    | exact resolve eq9 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq302 X0
       grind)
    | exact superpose eq302 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq302 X0
       grind)
    | exact superpose eq302 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq348 X0 X1
       have j1 := eq349 X0 X1
       grind)
    | (have r₁ := eq348 X0 X1
       have r₂ := eq349 X0 X1
       grind)
    | exact resolve eq348 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq429 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq350 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq350
    | exact resolve eq350 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq439 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq350 X1 X0
       grind)
    | exact superpose eq350 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq350 X1 (σ X1)
       grind)
    | (have r₁ := eq13 X1 (σ X0)
       have r₂ := eq350 X0 X1
       grind)
    | exact resolve eq13 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq350 y (σ x)
       grind)
    | exact superpose eq350 eq16
    | (have j1 := eq350 y (σ x)
       grind)
    | exact resolve eq16 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq445 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq439 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq447 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq443
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq443
    | exact resolve eq443 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq448 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq445 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq445 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq445 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq610 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq448 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq448
    | exact resolve eq448 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq672 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq610 X1 (τ X0)
       grind)
    | exact superpose eq610 eq17
    | (have j1 := eq610 X1 (τ X0)
       grind)
    | exact resolve eq17 eq610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq678 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq610 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1035 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq672 X1 (τ X0)
       grind)
    | exact superpose eq672 eq18
    | (have j1 := eq672 X1 (τ X0)
       grind)
    | exact resolve eq18 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq672
  have eq1040 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1035 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1035
    | (have j0 := eq1035 X0 X1
       grind)
    | exact resolve eq1035 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035
  have eq1051 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1040 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1040
    | (have j0 := eq1040 X0 X1
       grind)
    | exact resolve eq1040 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040
  have eq1052 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1051 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1051
    | (have j0 := eq1051 X0 X1
       grind)
    | exact resolve eq1051 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051
  have eq1109 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1052 X0 X1
       have i₂ := eq610 X0 X1
       grind)
    | exact superpose eq610 eq1052
    | (have j0 := eq1052 X1 X0
       have j1 := eq610 X1 X0
       grind)
    | exact resolve eq1052 eq610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq1114 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (σ (M.op (τ (σ X0)) (τ (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1052 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1052
    | exact resolve eq1052 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052
  have eq1174 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op (τ (σ X0)) X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1114 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1114
    | (have j0 := eq1114 X0 X1
       grind)
    | exact resolve eq1114 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114
  have eq1176 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1109 X0 X1
       have j1 := eq678 X0 X1
       grind)
    | (have r₁ := eq1109 X0 X1
       have r₂ := eq678 X0 X1
       grind)
    | exact resolve eq1109 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678 eq1109
  have eq1195 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1174 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1174
    | (have j0 := eq1174 X0 X1
       grind)
    | exact resolve eq1174 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174
  have eq1223 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq1176 X1 (σ X0)
       grind)
    | exact superpose eq1176 eq22
    | (have j1 := eq1176 X1 (σ X0)
       grind)
    | exact resolve eq22 eq1176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1176
  have eq1257 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1223 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1223
    | (have j0 := eq1223 X0 X1
       grind)
    | exact resolve eq1223 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223
  have eq1277 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1257 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1257
    | (have j0 := eq1257 X0 X1
       grind)
    | exact resolve eq1257 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257
  have eq1323 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1195 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195
  have eq1543 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1277 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1277
    | exact resolve eq1277 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277
  have eq1619 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1543 x y
       grind)
    | exact superpose eq1543 eq16
    | (have j1 := eq1543 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1543 x y
       grind)
    | exact resolve eq16 eq1543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543
  have eq1642 : y = (k x y) := by grind
  clear eq1619
  have eq1669 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq429 y x
       have i₂ := eq1642
       grind)
    | exact superpose eq1642 eq429
    | (have j0 := eq429 y x
       grind)
    | exact resolve eq429 eq1642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq1675 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 x
       have i₂ := eq1669
       grind)
    | exact superpose eq1669 eq9
    | exact resolve eq9 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1676 : ∀ X0 : G, y = (M.op y (M.op y (M.op X0 y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq1669
       grind)
    | exact superpose eq1669 eq9
    | exact resolve eq9 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1677 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq1694 : y = (M.op y (M.op y y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1675 x
       have i₂ := eq1669
       grind)
    | exact superpose eq1669 eq1675
    | exact resolve eq1675 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1669 eq1675
  have eq1701 : y = (M.op y (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1694
       have r₂ := eq1677
       grind)
    | exact resolve eq1694 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1677 eq1694
  have eq1712 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1676 y
       have i₂ := eq1701
       grind)
    | exact superpose eq1701 eq1676
    | exact resolve eq1676 eq1701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1676 eq1701
  have eq1719 : x = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq1712
  have eq1946 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq447
       have i₂ := eq1719
       grind)
    | exact superpose eq1719 eq447
    | exact resolve eq447 eq1719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447 eq1719
  have eq1952 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op y y) := by grind
  clear eq1946
  have eq1956 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1952
       have i₂ := eq1642
       grind)
    | exact superpose eq1642 eq1952
    | exact resolve eq1952 eq1642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1642 eq1952
  have eq1966 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq346 y (σ x)
       have i₂ := eq1956
       grind)
    | exact superpose eq1956 eq346
    | exact resolve eq346 eq1956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq1971 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op X0 (σ y)) (σ y))) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) X0 (σ x)
       have i₂ := eq1956
       grind)
    | exact superpose eq1956 eq9
    | exact resolve eq9 eq1956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11168 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1971 (σ x)
       have i₂ := eq1956
       grind)
    | exact superpose eq1956 eq1971
    | exact resolve eq1971 eq1956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1956 eq1971
  have eq11185 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by grind
  clear eq11168
  have eq11189 : (σ y) = (M.op (σ y) (σ (M.op y y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11185
       have i₂ := eq302 y
       grind)
    | exact superpose eq302 eq11185
    | exact resolve eq11185 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11185
  have eq11199 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1966
       have i₂ := eq11189
       grind)
    | exact superpose eq11189 eq1966
    | exact resolve eq1966 eq11189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1966 eq11189
  have eq11222 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq11199
  have eq11233 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq11222
       have i₂ := eq302 y
       grind)
    | exact superpose eq302 eq11222
    | exact resolve eq11222 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302 eq11222
  have eq11258 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq349 y X0
       have i₂ := eq11233
       grind)
    | exact superpose eq11233 eq349
    | (have j0 := eq349 y X0
       grind)
    | (have r₁ := eq349 y x
       have r₂ := eq11233
       grind)
    | exact resolve eq349 eq11233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11274 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (k y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1323 y y
       have i₂ := eq11233
       grind)
    | exact superpose eq11233 eq1323
    | (have j0 := eq1323 y y
       grind)
    | (have r₁ := eq1323 y y
       have r₂ := eq11233
       grind)
    | exact resolve eq1323 eq11233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11233
  have eq11275 : (σ y) = (σ (k y y)) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq11274
  have eq11278 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq11258 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11258
  have eq11280 : (σ y) = (σ (k y y)) := by
    first
    | (have j1 := eq1323 y y
       grind)
    | (have r₁ := eq11275
       have r₂ := eq1323 y y
       grind)
    | exact resolve eq11275 eq1323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323 eq11275
  have eq11282 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq11278 X0
       have j1 := eq349 y X0
       grind)
    | (have r₁ := eq11278 X0
       have r₂ := eq349 y x
       grind)
    | exact resolve eq11278 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349 eq11278
  have eq11283 : (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq11280
       have i₂ := eq272 y
       grind)
    | exact superpose eq272 eq11280
    | exact resolve eq11280 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272 eq11280
  have eq11291 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq11283
       grind)
    | exact superpose eq11283 eq10
    | exact resolve eq10 eq11283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11283
  have eq11369 : y = (M.op y y) := by
    first
    | (have i₁ := eq11291
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq11291
    | exact resolve eq11291 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11291
  have eq11557 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq11369
       grind)
    | exact superpose eq11369 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq11369
       grind)
    | exact resolve eq12 eq11369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11369
  have eq11583 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq11557 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11557
  have eq11900 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq11282 (σ X0)
       grind)
    | exact superpose eq11282 eq15
    | exact resolve eq15 eq11282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11282
  have eq11948 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq11900 X0
       have i₂ := eq11583 X0
       grind)
    | exact superpose eq11583 eq11900
    | exact resolve eq11900 eq11583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11583 eq11900
  have eq12240 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11948 x
       grind)
    | exact superpose eq11948 eq16
    | (have r₁ := eq16
       have r₂ := eq11948 x
       grind)
    | exact resolve eq16 eq11948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11948
  have eq12283 : False := by grind
  exact eq12283

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_pxx_pyx_Equation838 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law838 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq268 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq268 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq271 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq269 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq269 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq269 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq282 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq271 (σ X0)
       grind)
    | exact superpose eq271 eq15
    | exact resolve eq15 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq282 X0
       have i₂ := eq271 X0
       grind)
    | exact superpose eq271 eq282
    | exact resolve eq282 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq282
  have eq345 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq301 X0
       grind)
    | exact superpose eq301 eq9
    | exact resolve eq9 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq347 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq301 X0
       grind)
    | exact superpose eq301 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq301 X0
       grind)
    | exact superpose eq301 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq347 X0 X1
       have j1 := eq348 X0 X1
       grind)
    | (have r₁ := eq347 X0 X1
       have r₂ := eq348 X0 X1
       grind)
    | exact resolve eq347 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq507 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq349 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq349
    | exact resolve eq349 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq518 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq349 X0 (σ X1)
       grind)
    | exact superpose eq349 eq15
    | (have j1 := eq349 X0 (σ X1)
       grind)
    | exact resolve eq15 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq558 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq507 X0 (τ X1)
       grind)
    | exact superpose eq507 eq17
    | (have j1 := eq507 X0 (τ X1)
       grind)
    | exact resolve eq17 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq507
  have eq688 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq558 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq558
    | exact resolve eq558 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq737 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq688 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq688
    | (have j0 := eq688 X0 X1
       grind)
    | exact resolve eq688 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq1026 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq518 x y
       grind)
    | exact superpose eq518 eq16
    | (have j1 := eq518 x y
       grind)
    | exact resolve eq16 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq1092 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1026
       have i₂ := eq737 y x
       grind)
    | exact superpose eq737 eq1026
    | (have j1 := eq737 (σ y) (σ x)
       grind)
    | (have r₁ := eq1026
       have r₂ := eq737 y x
       grind)
    | exact resolve eq1026 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026
  have eq1093 : x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq1092
  have eq1097 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 x) x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq9 x X0 y
       have i₂ := eq1093
       grind)
    | exact superpose eq1093 eq9
    | exact resolve eq9 eq1093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1098 : ∀ X0 : G, x = (M.op x (M.op x (M.op X0 x))) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq1093
       grind)
    | exact superpose eq1093 eq9
    | exact resolve eq9 eq1093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1101 : x = (M.op x (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1097 y
       have i₂ := eq1093
       grind)
    | exact superpose eq1093 eq1097
    | exact resolve eq1097 eq1093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093 eq1097
  have eq1105 : x = (M.op x (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq1101
  have eq1113 : x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1098 x
       have i₂ := eq1105
       grind)
    | exact superpose eq1105 eq1098
    | exact resolve eq1098 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098 eq1105
  have eq1117 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq1113
  have eq1125 : (σ x) = (M.op (σ x) (M.op (σ x) (σ (M.op x x)))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq345 x (σ y)
       have i₂ := eq1117
       grind)
    | exact superpose eq1117 eq345
    | exact resolve eq345 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq1127 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (M.op X0 (σ x)) (σ x))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 (σ x) X0 (σ y)
       have i₂ := eq1117
       grind)
    | exact superpose eq1117 eq9
    | exact resolve eq9 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2374 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1127 (σ y)
       have i₂ := eq1117
       grind)
    | exact superpose eq1117 eq1127
    | exact resolve eq1127 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117 eq1127
  have eq2380 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by grind
  clear eq2374
  have eq2383 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2380
       have i₂ := eq301 x
       grind)
    | exact superpose eq301 eq2380
    | exact resolve eq2380 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2380
  have eq2385 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1125
       have i₂ := eq2383
       grind)
    | exact superpose eq2383 eq1125
    | exact resolve eq1125 eq2383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125 eq2383
  have eq2396 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq2385
  have eq2402 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2396
       have i₂ := eq301 x
       grind)
    | exact superpose eq301 eq2396
    | exact resolve eq2396 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301 eq2396
  have eq2413 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq348 x X0
       have i₂ := eq2402
       grind)
    | exact superpose eq2402 eq348
    | (have j0 := eq348 x X0
       grind)
    | (have r₁ := eq348 x x
       have r₂ := eq2402
       grind)
    | exact resolve eq348 eq2402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2402
  have eq2425 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq2413 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2413
  have eq2427 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq2425 X0
       have j1 := eq348 x X0
       grind)
    | (have r₁ := eq2425 X0
       have r₂ := eq348 x x
       grind)
    | exact resolve eq2425 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348 eq2425
  have eq2440 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq2427 (σ X0)
       grind)
    | exact superpose eq2427 eq15
    | exact resolve eq15 eq2427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2427
  have eq2563 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2440 y
       grind)
    | exact superpose eq2440 eq16
    | exact resolve eq16 eq2440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2440
  have eq2630 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2563
       have i₂ := eq737 y x
       grind)
    | exact superpose eq737 eq2563
    | (have j1 := eq737 y x
       grind)
    | (have r₁ := eq2563
       have r₂ := eq737 y x
       grind)
    | exact resolve eq2563 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq2631 : x = (M.op y x) := by grind
  clear eq2630
  have eq2638 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 x) x)) := by
    intro X0
    first
    | (have i₁ := eq9 x X0 y
       have i₂ := eq2631
       grind)
    | exact superpose eq2631 eq9
    | exact resolve eq9 eq2631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2639 : ∀ X0 : G, x = (M.op x (M.op x (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq2631
       grind)
    | exact superpose eq2631 eq9
    | exact resolve eq9 eq2631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2643 : x = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq2638 y
       have i₂ := eq2631
       grind)
    | exact superpose eq2631 eq2638
    | exact resolve eq2638 eq2631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2631 eq2638
  have eq2663 : x = (M.op x x) := by
    first
    | (have i₁ := eq2639 x
       have i₂ := eq2643
       grind)
    | exact superpose eq2643 eq2639
    | exact resolve eq2639 eq2643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2639 eq2643
  have eq2676 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq2663
       grind)
    | exact superpose eq2663 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq2663
       grind)
    | exact resolve eq12 eq2663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2663
  have eq2692 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq2676 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2676
  have eq2719 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq2563
       have i₂ := eq2692 y
       grind)
    | exact superpose eq2692 eq2563
    | exact resolve eq2563 eq2692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2563 eq2692
  have eq2722 : False := by grind
  exact eq2722

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation838 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law838 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq36 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
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
  have eq46 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq22
    | exact resolve eq22 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq101 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq96
    | (have j0 := eq96 X0 X1
       grind)
    | exact resolve eq96 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq135 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq101 X0 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq145 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq135 X0 X1 X2
       have i₂ := eq46 X0 X1
       grind)
    | exact superpose eq46 eq135
    | (have j0 := eq135 X0 X1 X2
       grind)
    | exact resolve eq135 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq135
  have eq319 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq47 X0 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq47
    | exact resolve eq47 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq332 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq319 X0
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq319
    | exact resolve eq319 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq5095 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) (k (σ X1) X2)) ≠ (M.op X3 (k (σ X1) X2)) ∨ (k (k (σ X1) X2) X3) = (M.op (σ X0) (k (σ X1) X2)) ∨ (k (σ X1) X2) = X3 ∨ (M.op (σ X0) (k (σ X1) X2)) = (σ (k (k X1 (τ X2)) X0)) ∨ (σ X0) = (k (σ X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (k (σ X0) X1) X1
       have i₂ := eq145 X0 X1 X2
       grind)
    | exact superpose eq145 eq13
    | (have j0 := eq13 (k (k (σ X1) X2) X3) (M.op (σ X0) (k (σ X1) X2))
       have j1 := eq145 X1 X2 X0
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (σ X2)
       have r₂ := eq145 X0 X1 X2
       grind)
    | exact resolve eq13 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq447231 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq5095 X2 X0 X1 (σ X2)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5095
  have eq447232 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq447231 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447231
  have eq447237 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq447232 X0 X1 X2
       have i₂ := eq36 X0 X1 X2
       grind)
    | exact superpose eq36 eq447232
    | (have j0 := eq447232 X0 X1 X2
       grind)
    | exact resolve eq447232 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq447232
  have eq447238 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq447237 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447237
  have eq447945 : ∀ X0 X1 X2 : G, (k (σ (k X1 (τ X2))) X0) = (M.op (σ (τ X0)) (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X0 (k X1 (τ X2))
       have i₂ := eq447238 X1 X2 (τ X0)
       grind)
    | exact superpose eq447238 eq19
    | (have j1 := eq447238 X1 X2 (τ X0)
       grind)
    | exact resolve eq19 eq447238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447238
  have eq448385 : ∀ X0 X1 X2 : G, (k (σ (k X1 (τ X2))) X0) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq447945 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq447945
    | (have j0 := eq447945 X0 X1 X2
       grind)
    | exact resolve eq447945 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447945
  have eq448574 : ∀ X0 X1 X2 : G, (k (k (σ X1) X2) X0) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq448385 X0 X1 X2
       have i₂ := eq19 X2 X1
       grind)
    | exact superpose eq19 eq448385
    | (have j0 := eq448385 X0 X1 X2
       grind)
    | exact resolve eq448385 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448385
  have eq448743 : ∀ X0 X1 X2 : G, (k (k (σ X1) X2) X0) = (M.op X0 (k (σ X1) X2)) ∨ (k (σ X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq448574 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq448574
    | (have j0 := eq448574 X0 X1 X2
       grind)
    | exact resolve eq448574 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448574
  have eq449033 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (M.op X2 (k X0 X1)) ∨ (k X0 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq448743 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq448743
    | exact resolve eq448743 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq449189 : ∀ X0 X1 : G, (k (M.op (σ X0) (σ X0)) X1) = (M.op X1 (M.op (σ X0) (σ X0))) ∨ (M.op (σ X0) (σ X0)) = X1 := by
    intro X0 X1
    grind
  clear eq448743
  have eq450072 : ∀ X0 X1 : G, (k (σ (M.op X0 X0)) X1) = (M.op X1 (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq449189 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq449189
    | (have j0 := eq449189 X0 X1
       grind)
    | exact resolve eq449189 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449189
  have eq450103 : ∀ X0 X1 : G, (k (σ (M.op X0 X0)) X1) = (M.op X1 (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq450072 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq450072
    | (have j0 := eq450072 X0 X1
       grind)
    | exact resolve eq450072 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450072
  have eq450771 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq458152 : ∀ X0 X1 : G, (k (M.op X1 X1) (τ X0)) = (τ (M.op X0 (σ (M.op X1 X1)))) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37 (M.op X1 X1) X0
       have i₂ := eq450103 X1 X0
       grind)
    | exact superpose eq450103 eq37
    | (have j1 := eq450103 X1 X0
       grind)
    | exact resolve eq37 eq450103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq450103
  have eq472446 : ∀ X0 : G, (τ (σ X0)) = (k (M.op (M.op X0 X0) (M.op X0 X0)) (τ (σ X0))) ∨ (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq458152 (σ X0) (M.op X0 X0)
       have i₂ := eq332 X0
       grind)
    | exact superpose eq332 eq458152
    | (have j0 := eq458152 (σ X0) (M.op X0 X0)
       grind)
    | exact resolve eq458152 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458152
  have eq472818 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq472446 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq472446
    | (have j0 := eq472446 X0
       grind)
    | exact resolve eq472446 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472446
  have eq522473 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq332 X0
       have i₂ := eq472818 X0
       grind)
    | exact superpose eq472818 eq332
    | (have j1 := eq472818 X0
       grind)
    | exact resolve eq332 eq472818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332 eq472818
  have eq523067 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq522473 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq522473
    | (have j0 := eq522473 X0
       grind)
    | exact resolve eq522473 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522473
  have eq523260 : ∀ X0 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq523067 X0
       grind)
    | exact superpose eq523067 eq10
    | (have j1 := eq523067 X0
       grind)
    | exact resolve eq10 eq523067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523067
  have eq523746 : ∀ X0 : G, (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq523260 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq523260
    | (have j0 := eq523260 X0
       grind)
    | exact resolve eq523260 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523260
  have eq525679 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq449033 (M.op (M.op X0 X0) (M.op X0 X0)) X0 x
       have i₂ := eq523746 X0
       grind)
    | exact superpose eq523746 eq449033
    | (have j0 := eq449033 X0 X1 (M.op X1 X0)
       have j1 := eq523746 X0
       grind)
    | exact resolve eq449033 eq523746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449033 eq523746
  have eq527614 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ X0 = X2 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq450771 X0 X1
       have i₂ := eq525679 X0 X1
       grind)
    | exact superpose eq525679 eq450771
    | (have j1 := eq525679 X0 X1
       grind)
    | exact resolve eq450771 eq525679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450771 eq525679
  have eq601776 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq527614 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527614
  have eq601777 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq601776 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601776
  have eq601778 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq601777 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601777
  have eq603035 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq601778 X1 (τ X0)
       grind)
    | exact superpose eq601778 eq19
    | (have j1 := eq601778 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq601778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq603403 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq601778 (σ X1) (σ X0)
       grind)
    | exact superpose eq601778 eq15
    | (have j1 := eq601778 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq601778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601778
  have eq607538 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq603035 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq603035
    | exact resolve eq603035 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603035
  have eq608276 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq607538 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq607538
    | (have j0 := eq607538 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq607538 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607538
  have eq620030 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq603403 x y
       grind)
    | exact superpose eq603403 eq16
    | (have j1 := eq603403 x y
       grind)
    | exact resolve eq16 eq603403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603403
  have eq622083 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq620030
       have i₂ := eq608276 x y
       grind)
    | exact superpose eq608276 eq620030
    | (have j1 := eq608276 (σ x) (σ y)
       grind)
    | (have r₁ := eq620030
       have r₂ := eq608276 x y
       grind)
    | (have r₁ := eq620030
       have r₂ := eq608276 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq620030
       have r₂ := eq608276 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq620030 eq608276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608276 eq620030
  have eq622086 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq622083
  have eq622090 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq622086
       grind)
    | exact superpose eq622086 eq16
    | exact resolve eq16 eq622086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622086
  have eq622091 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq622090
       have r₂ := eq22 x
       grind)
    | exact resolve eq622090 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622090
  have eq623626 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq622091
       grind)
    | exact superpose eq622091 eq16
    | exact resolve eq16 eq622091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq623627 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq622091
       grind)
    | exact superpose eq622091 eq10
    | exact resolve eq10 eq622091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622091
  have eq624155 : x = y := by
    first
    | (have i₁ := eq623627
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq623627
    | exact resolve eq623627 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623627
  have eq624156 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq623626
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq623626
    | exact resolve eq623626 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq623626
  have eq624163 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq624156
       have i₂ := eq624155
       grind)
    | exact superpose eq624155 eq624156
    | exact resolve eq624156 eq624155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624155 eq624156
  have eq624164 : False := by grind
  exact eq624164

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pyx_Equation838 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law838 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq329 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact superpose eq13 eq15
    | (have j1 := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq329 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq329
    | (have j0 := eq329 X0 X1
       grind)
    | exact resolve eq329 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq363 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq350 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq350
    | (have j0 := eq350 X0 X1
       grind)
    | (have r₁ := eq350 X0 X0
       have r₂ := eq22 X0
       grind)
    | exact resolve eq350 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq534 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq534 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq534
    | (have j0 := eq534 X0 X1
       grind)
    | exact resolve eq534 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq575 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq561 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq561
    | (have j0 := eq561 X0 X1
       grind)
    | exact resolve eq561 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq662 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq363 x y
       grind)
    | exact superpose eq363 eq16
    | (have j1 := eq363 x y
       grind)
    | exact resolve eq16 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq1467 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq575 x y
       grind)
    | exact superpose eq575 eq16
    | (have j1 := eq575 x y
       grind)
    | exact resolve eq16 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq6343 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x x) ≠ (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq662
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq662
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq662
       have r₂ := eq13 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq662
       have r₂ := eq13 (σ (k x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq662
       have r₂ := eq13 (σ (M.op x x)) (σ (M.op y y))
       grind)
    | exact resolve eq662 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq6344 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x x) ≠ (M.op y y) ∨ x = y := by grind
  clear eq6343
  have eq6350 : (M.op y y) = (τ (σ (M.op x x))) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1467
       grind)
    | exact superpose eq1467 eq10
    | exact resolve eq10 eq1467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467
  have eq6408 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6350
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq6350
    | exact resolve eq6350 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6350
  have eq6409 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq6408
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq6408
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq6408
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq6408
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq6408 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6408
  have eq6411 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6409
  have eq6412 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6411
  have eq8963 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq6344
       have i₂ := eq6412
       grind)
    | exact superpose eq6412 eq6344
    | (have r₁ := eq6344
       have r₂ := eq6412
       grind)
    | exact resolve eq6344 eq6412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6344 eq6412
  have eq8967 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x x) ≠ (M.op x x) ∨ x = y := by grind
  clear eq8963
  have eq8968 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq8967
  have eq8971 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq8968
       grind)
    | exact superpose eq8968 eq10
    | exact resolve eq10 eq8968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8968
  have eq9038 : x = y ∨ x = y := by
    first
    | (have i₁ := eq8971
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8971
    | exact resolve eq8971 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8971
  have eq9039 : x = y := by grind
  clear eq9038
  have eq9041 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9039
       grind)
    | exact superpose eq9039 eq16
    | exact resolve eq16 eq9039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9039
  have eq9049 : False := by grind
  exact eq9049

/-- `Equation840`: `x = x ◇ ((y ◇ x) ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_x_pxy_y_pyx_Equation840 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law840 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law840.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2))) = X0 := by
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
  have eq53 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq53 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 x y
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 (σ x) (σ y)
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X1)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq13
    | (have r₁ := eq13 X1 (M.op X0 X1)
       have r₂ := eq53 X0 X1
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : x ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : y ≠ y ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq54 eq13
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq54
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq69 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq55 eq13
    | (have r₁ := eq13 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq55
       grind)
    | exact resolve eq13 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq70 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by grind
  clear eq69
  have eq71 : y = (k y (M.op x y)) := by grind
  clear eq67
  have eq72 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq74 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq60 eq13
    | (have r₁ := eq13 (M.op x y) y
       have r₂ := eq60
       grind)
    | exact resolve eq13 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq77 : (M.op x y) = (k (M.op x y) y) := by grind
  clear eq74
  have eq78 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq62 eq13
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ y)
       have r₂ := eq62
       grind)
    | exact resolve eq13 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq81 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by grind
  clear eq78
  have eq84 : y ≠ (M.op x y) ∨ y = (M.op y x) ∨ x = (k y x) := by
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
  have eq87 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq113 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq72 (M.op X1 X0) X0
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq72
    | exact resolve eq72 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq128 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq131 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq71 eq128
    | exact resolve eq128 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq128
  have eq132 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq131
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq131
    | exact resolve eq131 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq134 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq132 eq11
    | (have j0 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq135 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq134
  have eq142 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq159 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq77 eq155
    | exact resolve eq155 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq155
  have eq160 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq159
    | exact resolve eq159 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq162 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq160 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq11 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq162
  have eq165 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq126
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq126
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq126 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq126
       grind)
    | exact superpose eq126 eq16
    | exact resolve eq16 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq165
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq165
    | exact resolve eq165 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq173 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq172
    | exact resolve eq172 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq174 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq173
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq173
    | exact resolve eq173 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq666 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq90 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq90 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq90 X0 X0
       grind)
    | exact resolve eq12 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq670 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (σ X1) (σ X0)
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq53
    | (have j1 := eq90 X0 X1
       grind)
    | exact resolve eq53 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq675 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq90 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq678 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq666 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq692 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq678 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq678 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq678 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq678 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq701 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq692 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq692
    | (have j0 := eq692 X0 X1
       grind)
    | exact resolve eq692 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq958 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq135 eq53
    | exact resolve eq53 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq1022 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq163 eq12
    | (have j0 := eq12 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) (σ y)
       have r₂ := eq163
       grind)
    | exact resolve eq12 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq1033 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (k (σ (M.op x y)) (σ y)) := by grind
  clear eq1022
  have eq1034 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (k (σ (M.op x y)) (σ y)) := by grind
  clear eq1033
  have eq1036 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq160 eq1034
    | exact resolve eq1034 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034
  have eq1148 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq958
  have eq1151 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq1148
       have r₂ := eq1036
       grind)
    | exact resolve eq1148 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036 eq1148
  have eq6199 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq701 X0 (M.op X1 X0)
       have i₂ := eq72 X0 X1
       grind)
    | exact superpose eq72 eq701
    | (have j0 := eq701 X0 (M.op X1 X0)
       grind)
    | exact resolve eq701 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq6345 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (M.op X1 X0))) ∨ (σ X0) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq6199 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6199
  have eq14167 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq174 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14174 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq14167
    | exact resolve eq14167 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14167
  have eq14185 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq14174
       have r₂ := eq27
       grind)
    | exact resolve eq14174 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14174
  have eq14189 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq14185
    | exact resolve eq14185 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14185
  have eq14622 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq14189 eq53
    | exact resolve eq53 eq14189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14189
  have eq14641 : y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq14622
    | exact resolve eq14622 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14622
  have eq14654 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq113 x y
       have i₂ := eq14641
       grind)
    | exact superpose eq14641 eq113
    | exact resolve eq113 eq14641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14641
  have eq16059 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq675 x y
       have i₂ := eq14654
       grind)
    | exact superpose eq14654 eq675
    | (have j0 := eq675 x y
       grind)
    | exact resolve eq675 eq14654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675 eq14654
  have eq16063 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16059
  have eq16068 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16063
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16063
    | exact resolve eq16063 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16063
  have eq16082 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16068
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16068
    | exact resolve eq16068 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16068
  have eq16092 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq16082
    | exact resolve eq16082 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16082
  have eq16093 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16092
  have eq16099 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16093
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16093
    | exact resolve eq16093 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16093
  have eq16109 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16099
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16099
    | exact resolve eq16099 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16099
  have eq16356 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16109 eq53
    | exact resolve eq53 eq16109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16109
  have eq16377 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq16356
    | exact resolve eq16356 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16356
  have eq16378 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq16377
  have eq16474 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16378 eq27
    | exact resolve eq27 eq16378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16482 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16378 eq87
    | (have r₁ := eq87
       have r₂ := eq16378
       grind)
    | exact resolve eq87 eq16378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq16491 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq16378
  have eq16492 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq16482
  have eq42741 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16492 eq53
    | exact resolve eq53 eq16492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16492
  have eq42787 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq42741
    | exact resolve eq42741 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42741
  have eq42788 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq42787
  have eq42799 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq42788 eq174
    | exact resolve eq174 eq42788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq42788
  have eq42840 : y = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq42799
  have eq50450 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6345 x y
       have i₂ := eq42840
       grind)
    | exact superpose eq42840 eq6345
    | exact resolve eq6345 eq42840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6345 eq42840
  have eq50609 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50450
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq50450
    | exact resolve eq50450 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50450
  have eq50673 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50609
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq50609
    | exact resolve eq50609 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50609
  have eq50723 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq50673
    | exact resolve eq50673 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50673
  have eq50724 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq50723
  have eq50732 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq50724
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq50724
    | exact resolve eq50724 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50724
  have eq50739 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq50732
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq50732
    | exact resolve eq50732 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50732
  have eq50746 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq50739
       have r₂ := eq16491
       grind)
    | exact resolve eq50739 eq16491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16491 eq50739
  have eq50767 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq50746 eq70
    | exact resolve eq70 eq50746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq50768 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq50746 eq81
    | exact resolve eq81 eq50746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq50915 : (τ (σ y)) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq50767 eq171
    | exact resolve eq171 eq50767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171 eq50767
  have eq50969 : y = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq50915
    | exact resolve eq50915 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq50915
  have eq83886 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq50969
       grind)
    | exact superpose eq50969 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq50969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50969
  have eq83897 : y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq83886
  have eq83912 : y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq83897
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq83897
    | exact resolve eq83897 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83897
  have eq83913 : y = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq83912
  have eq84080 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq83913
       grind)
    | exact superpose eq83913 eq53
    | exact resolve eq53 eq83913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83913
  have eq84130 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq84080
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq84080
    | exact resolve eq84080 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84080
  have eq84144 : (k x y) = (τ (k (σ (M.op x y)) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq84130 eq142
    | exact resolve eq142 eq84130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq84130
  have eq84382 : (τ (σ (M.op x y))) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq160 eq84144
    | exact resolve eq84144 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq84144
  have eq84434 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq84382
    | exact resolve eq84382 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq84382
  have eq84454 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq84434
       have r₂ := eq66
       grind)
    | exact resolve eq84434 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq84434
  have eq85243 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq84454
       grind)
    | exact superpose eq84454 eq44
    | exact resolve eq44 eq84454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq85272 : (σ x) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq701 x y
       have i₂ := eq84454
       grind)
    | exact superpose eq84454 eq701
    | (have j0 := eq701 x y
       grind)
    | exact resolve eq701 eq84454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701 eq84454
  have eq85293 : (σ x) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq85272
    | exact resolve eq85272 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85272
  have eq85310 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq85243
    | exact resolve eq85243 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85243
  have eq85313 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq85293
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq85293
    | exact resolve eq85293 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85293
  have eq85325 : (σ y) = (σ (M.op x y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq85313
    | exact resolve eq85313 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85313
  have eq85333 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq85325
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq85325
    | exact resolve eq85325 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85325
  have eq85341 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq85333
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq85333
    | exact resolve eq85333 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85333
  have eq85349 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq85341
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq85341
    | exact resolve eq85341 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85341
  have eq85357 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq85349
    | exact resolve eq85349 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85349
  have eq85365 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq85357
       have r₂ := eq16474
       grind)
    | exact resolve eq85357 eq16474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16474 eq85357
  have eq85369 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq85365
       have r₂ := eq50746
       grind)
    | exact resolve eq85365 eq50746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50746 eq85365
  have eq85381 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq85369 eq27
    | exact resolve eq27 eq85369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85369
  have eq86192 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq85310 eq50768
    | exact resolve eq50768 eq85310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50768 eq85310
  have eq86206 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq86192
  have eq86232 : y = (M.op x y) := by
    first
    | (have r₁ := eq86206
       have r₂ := eq85381
       grind)
    | exact resolve eq86206 eq85381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85381 eq86206
  have eq86592 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq86232 eq20
    | exact resolve eq20 eq86232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq86601 : y ≠ y ∨ y = (M.op y x) ∨ x = (k y x) := by
    first
    | exact superpose eq86232 eq84
    | (have r₁ := eq84
       have r₂ := eq86232
       grind)
    | exact resolve eq84 eq86232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq86759 : y = (M.op y x) ∨ x = (k y x) := by grind
  clear eq86601
  have eq86847 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq86592
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq86592
    | exact resolve eq86592 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86592
  have eq86881 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq86847 eq26
    | exact resolve eq26 eq86847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq86940 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq86847 eq1151
    | exact resolve eq1151 eq86847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151
  have eq99577 : x = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq86759
       grind)
    | exact superpose eq86759 eq53
    | exact resolve eq53 eq86759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86759
  have eq99623 : x = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq99577
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq99577
    | exact resolve eq99577 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq99577
  have eq99627 : x = (k y x) ∨ x = y := by
    first
    | exact superpose eq86232 eq99623
    | exact resolve eq99623 eq86232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86232 eq99623
  have eq99644 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq126
       have i₂ := eq99627
       grind)
    | exact superpose eq99627 eq126
    | exact resolve eq126 eq99627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq99672 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq670 y x
       have i₂ := eq99627
       grind)
    | exact superpose eq99627 eq670
    | (have j0 := eq670 y x
       grind)
    | exact resolve eq670 eq99627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670 eq99627
  have eq99678 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq99672
  have eq99693 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq99678
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq99678
    | exact resolve eq99678 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99678
  have eq99710 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = y := by
    first
    | exact superpose eq86847 eq99644
    | exact resolve eq99644 eq86847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99644
  have eq99716 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq99693
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq99693
    | exact resolve eq99693 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99693
  have eq99729 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq99710
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq99710
    | exact resolve eq99710 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99710
  have eq99735 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq86847 eq99716
    | exact resolve eq99716 eq86847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99716
  have eq99749 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq99735
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq99735
    | exact resolve eq99735 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99735
  have eq99759 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = y := by
    first
    | exact superpose eq86847 eq99749
    | exact resolve eq99749 eq86847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99749
  have eq99767 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq99759
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq99759
    | exact resolve eq99759 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99759
  have eq99774 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = y := by
    first
    | exact superpose eq86881 eq99767
    | exact resolve eq99767 eq86881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99767
  have eq99781 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq99774
       have r₂ := eq27
       grind)
    | exact resolve eq99774 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99774
  have eq100387 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq99781 eq53
    | exact resolve eq53 eq99781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq100395 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y := by
    first
    | exact superpose eq99781 eq113
    | exact resolve eq113 eq99781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq99781
  have eq100434 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq86881 eq100387
    | exact resolve eq100387 eq86881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100387
  have eq100958 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq100434 eq27
    | exact resolve eq27 eq100434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100434
  have eq101844 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq100395 eq99729
    | exact resolve eq99729 eq100395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99729 eq100395
  have eq101862 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq101844
  have eq101870 : x = y := by
    first
    | (have r₁ := eq101862
       have r₂ := eq100958
       grind)
    | exact resolve eq101862 eq100958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100958 eq101862
  have eq101902 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq101870
       grind)
    | exact superpose eq101870 eq24
    | exact resolve eq24 eq101870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq101870
  have eq102546 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq86847 eq101902
    | exact resolve eq101902 eq86847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86847 eq101902
  have eq102774 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq102546
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq102546
    | exact resolve eq102546 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq102546
  have eq103053 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq102774 eq86881
    | exact resolve eq86881 eq102774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86881 eq102774
  have eq103067 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq86940 eq103053
    | exact resolve eq103053 eq86940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86940 eq103053
  have eq103134 : False := by grind
  exact eq103134

/-- `Equation840`: `x = x ◇ ((y ◇ x) ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then X else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_x_pxy_pyx_Equation840 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law840 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law840.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2))) = X0 := by
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
  have eq50 : x ≠ (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq59 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq59
    | (have j0 := eq59 x y
       grind)
    | exact resolve eq59 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq59
    | (have j0 := eq59 (σ x) (σ y)
       grind)
    | exact resolve eq59 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X1 X0)
       have i₂ := eq59 X1 X0
       grind)
    | exact superpose eq59 eq13
    | (have j0 := eq13 X0 (M.op X1 X0)
       grind)
    | (have r₁ := eq13 X1 (M.op X0 X1)
       have r₂ := eq59 X0 X1
       grind)
    | exact resolve eq13 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq72 : y ≠ y ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq62 eq13
    | (have j0 := eq13 y (M.op x y)
       grind)
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq62
       grind)
    | exact resolve eq13 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : y = (k y (M.op x y)) := by grind
  clear eq72
  have eq76 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq63 eq13
    | (have j0 := eq13 (σ y) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq63
       grind)
    | exact resolve eq13 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq77 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by grind
  clear eq76
  have eq78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq83 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
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
  have eq85 : x = (M.op x y) ∨ (k (σ x) (σ y)) = (σ (M.op y x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq83
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq83
    | exact resolve eq83 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq119 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq120 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq121 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq11 sF3 (σ X0)
       grind)
    | exact superpose eq11 eq36
    | (have j1 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq36 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq73 eq121
    | exact resolve eq121 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq124
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq124
    | exact resolve eq124 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq126 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq125
       have i₂ := eq11 sF3 sF1
       grind)
    | exact superpose eq11 eq125
    | (have j1 := eq11 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq125 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq119
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq119
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq119 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq157
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq157
    | exact resolve eq157 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq165 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq164
    | exact resolve eq164 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq166 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq165
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq165
    | exact resolve eq165 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq173 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq120
       grind)
    | exact superpose eq120 eq16
    | exact resolve eq16 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq654 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq78 X0 X1
       grind)
    | exact superpose eq78 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq78 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq78 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq12 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X1) (σ X0)
       have i₂ := eq78 X0 X1
       grind)
    | exact superpose eq78 eq59
    | (have j1 := eq78 X0 X1
       grind)
    | exact resolve eq59 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq666 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq654 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq680 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq666 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq666 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq666 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq666 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq690 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq680 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq680
    | (have j0 := eq680 X0 X1
       grind)
    | exact resolve eq680 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq5701 : ∀ X0 : G, (σ y) = (k (σ y) (σ (k y X0))) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq122 eq69
    | (have j1 := eq122 X0
       grind)
    | exact resolve eq69 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq5713 : ∀ X0 : G, (σ y) = (σ (k y (k y X0))) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq5701
    | (have j0 := eq5701 X0
       grind)
    | exact resolve eq5701 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq5701
  have eq7177 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq166 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7178 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq7177
    | exact resolve eq7177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7177
  have eq7189 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq7178
       have r₂ := eq27
       grind)
    | exact resolve eq7178 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7178
  have eq7193 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq7189
    | exact resolve eq7189 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7189
  have eq7752 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq7193 eq59
    | exact resolve eq59 eq7193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7193
  have eq7768 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq7752
    | exact resolve eq7752 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7752
  have eq7769 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7768
  have eq7777 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq59 y x
       have i₂ := eq7769
       grind)
    | exact superpose eq7769 eq59
    | exact resolve eq59 eq7769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7782 : x = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq69 x y
       have i₂ := eq7769
       grind)
    | exact superpose eq7769 eq69
    | exact resolve eq69 eq7769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq7769
  have eq7792 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq7782
       have r₂ := eq50
       grind)
    | exact resolve eq7782 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq7782
  have eq7793 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7777
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7777
    | exact resolve eq7777 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7777
  have eq7794 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq7793
  have eq7804 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7794 eq77
    | exact resolve eq77 eq7794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq7794
  have eq7926 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq7792
       grind)
    | exact superpose eq7792 eq44
    | exact resolve eq44 eq7792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7792
  have eq7943 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7926
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7926
    | exact resolve eq7926 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7926
  have eq7946 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq7943
       have r₂ := eq51
       grind)
    | exact resolve eq7943 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq7943
  have eq8157 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7804 eq166
    | exact resolve eq166 eq7804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166 eq7804
  have eq8166 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq8157
  have eq9850 : (σ x) = (M.op (σ x) (k (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq658 x y
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq658
    | (have j0 := eq658 x y
       grind)
    | exact resolve eq658 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq9862 : (σ y) = (M.op (σ y) (k (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq658 y x
       have i₂ := eq119
       grind)
    | exact superpose eq119 eq658
    | (have j0 := eq658 y x
       grind)
    | exact resolve eq658 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq658
  have eq9924 : (σ y) = (M.op (σ y) (k (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq9862
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9862
    | exact resolve eq9862 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9862
  have eq9936 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7946 eq9850
    | exact resolve eq9850 eq7946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9850
  have eq10030 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (k (σ y) (σ x))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq9924
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9924
    | exact resolve eq9924 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9924
  have eq10042 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9936
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9936
    | exact resolve eq9936 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9936
  have eq10129 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (k (σ y) (σ x))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10030
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10030
    | exact resolve eq10030 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10030
  have eq10141 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10042
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10042
    | exact resolve eq10042 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10042
  have eq10221 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (k (σ y) (σ x))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq10129
    | exact resolve eq10129 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10129
  have eq10233 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10141
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10141
    | exact resolve eq10141 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10141
  have eq10309 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq10221
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10221
    | exact resolve eq10221 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10221
  have eq10321 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10233
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10233
    | exact resolve eq10233 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10233
  have eq10379 : (σ y) = (M.op (σ y) (k (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10309
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10309
    | exact resolve eq10309 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10309
  have eq10381 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10321
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10321
    | exact resolve eq10321 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10321
  have eq10400 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq10381
    | exact resolve eq10381 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10381
  have eq11307 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq59 y x
       have i₂ := eq8166
       grind)
    | exact superpose eq8166 eq59
    | exact resolve eq59 eq8166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8166
  have eq11324 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq11307
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11307
    | exact resolve eq11307 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11307
  have eq11325 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq11324
  have eq11332 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11325 eq29
    | exact resolve eq29 eq11325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11325
  have eq11438 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq11332
    | exact resolve eq11332 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq11332
  have eq12218 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11438 eq62
    | exact resolve eq62 eq11438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq12270 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq13077 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) y)) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 y
       have i₂ := eq12218
       grind)
    | exact superpose eq12218 eq14
    | exact resolve eq14 eq12218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12218
  have eq17008 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq10400 eq59
    | exact resolve eq59 eq10400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10400
  have eq17031 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq17008
    | exact resolve eq17008 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17008
  have eq17032 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17031
  have eq17101 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 X0))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq17032 eq14
    | exact resolve eq14 eq17032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17032
  have eq38127 : (σ x) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq7946 eq85
    | exact resolve eq85 eq7946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq7946
  have eq38243 : (τ (σ x)) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16 (M.op y x)
       have i₂ := eq38127
       grind)
    | exact superpose eq38127 eq16
    | exact resolve eq16 eq38127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38127
  have eq38319 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28 eq38243
    | exact resolve eq38243 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq38243
  have eq456181 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq59 y x
       have i₂ := eq38319
       grind)
    | exact superpose eq38319 eq59
    | exact resolve eq59 eq38319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38319
  have eq456289 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq456181
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq456181
    | exact resolve eq456181 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456181
  have eq456290 : x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq456289
  have eq456401 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13077 x y
       have i₂ := eq456290
       grind)
    | exact superpose eq456290 eq13077
    | exact resolve eq13077 eq456290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13077 eq456290
  have eq456420 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq456401
  have eq456430 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq456420
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq456420
    | exact resolve eq456420 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456420
  have eq459085 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq11438 eq456430
    | exact resolve eq456430 eq11438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11438 eq456430
  have eq459210 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq459085
       have r₂ := eq12270
       grind)
    | exact resolve eq459085 eq12270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12270 eq459085
  have eq459214 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq459210
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq459210
    | exact resolve eq459210 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq459210
  have eq459215 : x = (M.op x y) := by grind
  clear eq459214
  have eq459217 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq459215 eq20
    | exact resolve eq20 eq459215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq459224 : y = (k y x) := by
    first
    | exact superpose eq459215 eq73
    | exact resolve eq73 eq459215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq459215
  have eq459589 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq459217
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq459217
    | exact resolve eq459217 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459217
  have eq460074 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq459589 eq26
    | exact resolve eq26 eq459589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq460200 : (σ y) = (M.op (σ y) (k (σ y) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq459589 eq10379
    | exact resolve eq10379 eq459589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10379
  have eq460264 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op X0 X0))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq459589 eq17101
    | exact resolve eq17101 eq459589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17101
  have eq460761 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq460264 X0
       grind)
    | (have r₁ := eq460264 X0
       have r₂ := eq27
       grind)
    | exact resolve eq460264 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460264
  have eq460783 : (σ y) = (M.op (σ y) (k (σ y) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq460200
       have r₂ := eq27
       grind)
    | exact resolve eq460200 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460200
  have eq460879 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq125 eq460783
    | exact resolve eq460783 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq460783
  have eq461139 : (σ y) = (σ (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq5713 x
       have i₂ := eq459224
       grind)
    | exact superpose eq459224 eq5713
    | (have j0 := eq5713 x
       grind)
    | exact resolve eq5713 eq459224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5713 eq459224
  have eq461190 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq461139
       have i₂ := eq120
       grind)
    | exact superpose eq120 eq461139
    | exact resolve eq461139 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq461139
  have eq461247 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq461190
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq461190
    | exact resolve eq461190 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461190
  have eq461304 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq461247
    | exact resolve eq461247 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq461247
  have eq461344 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq459589 eq461304
    | exact resolve eq461304 eq459589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461304
  have eq461383 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq461344
       have r₂ := eq27
       grind)
    | exact resolve eq461344 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461344
  have eq461416 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq461383
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq461383
    | exact resolve eq461383 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq461383
  have eq461444 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq459589 eq461416
    | exact resolve eq461416 eq459589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459589 eq461416
  have eq590213 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq460879 eq460761
    | exact resolve eq460761 eq460879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460761 eq460879
  have eq590352 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq460074 eq590213
    | exact resolve eq590213 eq460074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590213
  have eq591233 : (τ (σ y)) = (k y y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq461444 eq173
    | exact resolve eq173 eq461444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173 eq461444
  have eq591514 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (k y y) := by
    first
    | exact superpose eq29 eq591233
    | exact resolve eq591233 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq591233
  have eq594886 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq590352 eq59
    | exact resolve eq59 eq590352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590352
  have eq595002 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq460074 eq594886
    | exact resolve eq594886 eq460074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594886
  have eq595010 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq595002
       have r₂ := eq27
       grind)
    | exact resolve eq595002 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595002
  have eq623367 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq591514 eq59
    | exact resolve eq59 eq591514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq591514
  have eq623488 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq460074 eq623367
    | exact resolve eq623367 eq460074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623367
  have eq623496 : y = (k y y) := by
    first
    | (have r₁ := eq623488
       have r₂ := eq27
       grind)
    | exact resolve eq623488 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623488
  have eq623702 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq690 y y
       have i₂ := eq623496
       grind)
    | exact superpose eq623496 eq690
    | (have j0 := eq690 y y
       grind)
    | exact resolve eq690 eq623496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690 eq623496
  have eq623727 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq623702
  have eq623728 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq623727
  have eq623763 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq623728
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq623728
    | exact resolve eq623728 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq623728
  have eq632136 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) (σ y))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq623763 eq14
    | exact resolve eq14 eq623763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq726035 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq126 eq632136
    | exact resolve eq632136 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq632136
  have eq726302 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq623763 eq726035
    | exact resolve eq726035 eq623763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623763 eq726035
  have eq726303 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq726302
  have eq726495 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq460074 eq726303
    | exact resolve eq726303 eq460074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726303
  have eq726592 : (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq726495
       have r₂ := eq27
       grind)
    | exact resolve eq726495 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726495
  have eq726663 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq460074 eq726592
    | exact resolve eq726592 eq460074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726592
  have eq727126 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq726663 eq595010
    | exact resolve eq595010 eq726663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595010 eq726663
  have eq727200 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq460074 eq727126
    | exact resolve eq727126 eq460074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460074 eq727126
  have eq727227 : False := by grind
  exact eq727227
