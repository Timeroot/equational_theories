import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,Y) else if X = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pyy_pyy_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq23
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq15
    | exact resolve eq15 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq67 (τ X0)
       grind)
    | exact superpose eq67 eq32
    | exact resolve eq32 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq73
    | exact resolve eq73 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq71
    | exact resolve eq71 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq71
  have eq103 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ X0)
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq12
    | exact resolve eq12 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq592 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq600 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
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
  clear eq18
  have eq611 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq592 X0 X1
       have i₂ := eq82 X1
       grind)
    | exact superpose eq82 eq592
    | (have j0 := eq592 X0 X1
       grind)
    | exact resolve eq592 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq631 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq611 x y
       grind)
    | exact superpose eq611 eq16
    | (have j1 := eq611 x y
       grind)
    | exact resolve eq16 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq636 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq611 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq3065 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq600 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq600
    | exact resolve eq600 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq3123 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3065 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3065
    | (have j0 := eq3065 X0 X1
       grind)
    | exact resolve eq3065 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3065
  have eq6134 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq631
       have i₂ := eq3123 x y
       grind)
    | exact superpose eq3123 eq631
    | (have j1 := eq3123 x y
       grind)
    | (have r₁ := eq631
       have r₂ := eq3123 x y
       grind)
    | (have r₁ := eq631
       have r₂ := eq3123 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq631
       have r₂ := eq3123 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq631 eq3123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631 eq3123
  have eq6135 : x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq6134
  have eq8029 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq636 (τ X0) (τ X1)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq636
    | (have j0 := eq636 (τ X0) (τ X1)
       grind)
    | exact resolve eq636 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq8095 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (τ (M.op X1 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8029 X0 X1
       have i₂ := eq80 X1
       grind)
    | exact superpose eq80 eq8029
    | (have j0 := eq8029 X0 X1
       grind)
    | exact resolve eq8029 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8029
  have eq8129 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8095 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq8095
    | (have j0 := eq8095 X0 X1
       grind)
    | exact resolve eq8095 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8095
  have eq8158 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8129 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq8129
    | (have j0 := eq8129 X0 X1
       grind)
    | exact resolve eq8129 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8129
  have eq8183 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8158 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq8158
    | (have j0 := eq8158 X0 X1
       grind)
    | exact resolve eq8158 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8158
  have eq8204 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = (σ (τ (M.op X1 X1))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8183 X0 X1
       have i₂ := eq80 X1
       grind)
    | exact superpose eq80 eq8183
    | (have j0 := eq8183 X0 X1
       grind)
    | exact resolve eq8183 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq8183
  have eq8224 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8204 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq8204
    | (have j0 := eq8204 X0 X1
       grind)
    | exact resolve eq8204 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8204
  have eq8239 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8224 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8224
    | (have j0 := eq8224 X0 X1
       grind)
    | exact resolve eq8224 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8224
  have eq8253 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8239 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq8239
    | (have j0 := eq8239 X0 X1
       grind)
    | exact resolve eq8239 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8239
  have eq8262 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8253 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8253
    | (have j0 := eq8253 X0 X1
       grind)
    | exact resolve eq8253 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8253
  have eq30214 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6135
       grind)
    | exact superpose eq6135 eq16
    | exact resolve eq16 eq6135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6135
  have eq30215 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq30214
       have r₂ := eq82 x
       grind)
    | exact resolve eq30214 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30214
  have eq30219 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq103 y (σ x)
       have i₂ := eq30215
       grind)
    | exact superpose eq30215 eq103
    | (have j0 := eq103 y (σ x)
       grind)
    | (have r₁ := eq103 y (σ x)
       have r₂ := eq30215
       grind)
    | exact resolve eq103 eq30215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq30215
  have eq30266 : (σ (M.op y y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq30219
  have eq30271 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq30266
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq30266
    | exact resolve eq30266 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30266
  have eq30276 : y = (τ (σ x)) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq30271
       grind)
    | exact superpose eq30271 eq10
    | exact resolve eq10 eq30271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30271
  have eq30464 : x = y ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq30276
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq30276
    | exact resolve eq30276 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30276
  have eq30466 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30464
       grind)
    | exact superpose eq30464 eq16
    | exact resolve eq16 eq30464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30464
  have eq30467 : (σ (k x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq30466
       have r₂ := eq82 x
       grind)
    | exact resolve eq30466 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30466
  have eq30476 : (k x y) = (τ (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq30467
       grind)
    | exact superpose eq30467 eq10
    | exact resolve eq10 eq30467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30467
  have eq30670 : (k x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq30476
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq30476
    | exact resolve eq30476 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30476
  have eq30671 : (k x y) = (M.op y y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq30670
       have r₂ := eq12 x y
       grind)
    | exact resolve eq30670 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30670
  have eq30677 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq636 x y
       have i₂ := eq30671
       grind)
    | exact superpose eq30671 eq636
    | (have j0 := eq636 x y
       grind)
    | exact resolve eq636 eq30671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq30695 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq8262 x y
       have i₂ := eq30671
       grind)
    | exact superpose eq30671 eq8262
    | (have j0 := eq8262 x y
       grind)
    | (have r₁ := eq8262 x y
       have r₂ := eq30671
       grind)
    | exact resolve eq8262 eq30671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8262 eq30671
  have eq30698 : x = y ∨ (M.op x y) = (M.op y y) := by grind
  clear eq30695
  have eq30699 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by grind
  clear eq30677
  have eq30702 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30698
       grind)
    | exact superpose eq30698 eq16
    | exact resolve eq16 eq30698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30698
  have eq30704 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq30702
       have r₂ := eq82 x
       grind)
    | exact resolve eq30702 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30702
  have eq31706 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30699
       grind)
    | exact superpose eq30699 eq16
    | exact resolve eq16 eq30699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30699
  have eq31763 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq31706
       have i₂ := eq30704
       grind)
    | exact superpose eq30704 eq31706
    | exact resolve eq31706 eq30704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30704 eq31706
  have eq31764 : (σ x) = (σ y) := by grind
  clear eq31763
  have eq31767 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31764
       grind)
    | exact superpose eq31764 eq16
    | exact resolve eq16 eq31764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31770 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq31764
       grind)
    | exact superpose eq31764 eq10
    | exact resolve eq10 eq31764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31764
  have eq31999 : x = y := by
    first
    | (have i₁ := eq31770
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq31770
    | exact resolve eq31770 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31770
  have eq32000 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq31767
       have i₂ := eq82 x
       grind)
    | exact superpose eq82 eq31767
    | exact resolve eq31767 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq31767
  have eq32006 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq32000
       have i₂ := eq31999
       grind)
    | exact superpose eq31999 eq32000
    | exact resolve eq32000 eq31999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31999 eq32000
  have eq32007 : False := by grind
  exact eq32007

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_pxy_pxy_pxx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq19 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq27 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq27 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq40 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq40 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq40 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq44 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq41 (σ X0)
       grind)
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq41 (τ X0)
       grind)
    | exact superpose eq41 eq17
    | exact resolve eq17 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq45 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq45
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq47 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq44 X0
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq44
    | exact resolve eq44 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq50 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq46
    | exact resolve eq46 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq46
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 X1
       have i₂ := eq47 X0
       grind)
    | exact superpose eq47 eq72
    | (have j0 := eq72 X0 X1
       grind)
    | exact resolve eq72 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq97 : ∀ X0 X1 : G, (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq47
    | exact resolve eq47 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (M.op X2 (M.op (τ X0) (τ X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (M.op X1 (M.op X2 (M.op (τ X0) (τ X0))))
       have i₂ := eq30 (τ X0) X1 X2
       grind)
    | exact superpose eq30 eq17
    | exact resolve eq17 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (M.op X2 (M.op (τ X0) (τ X0)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq117 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq117
    | exact resolve eq117 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq131 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq10
    | exact resolve eq10 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq19 X1 X0 X3
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq174 : ∀ X0 X1 X2 : G, (τ X0) = (k (τ X0) (M.op X1 (M.op X2 (τ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 (τ X0) X1 X2
       have i₂ := eq131 X0
       grind)
    | exact superpose eq131 eq30
    | exact resolve eq30 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (τ X0)
       have i₂ := eq131 X0
       grind)
    | exact superpose eq131 eq20
    | exact resolve eq20 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq207 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq76 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq76
    | exact resolve eq76 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76 (k (τ X0) X1) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq76
    | exact resolve eq76 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq237 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq208 X0 X1 X2
       have i₂ := eq97 X0 X1
       grind)
    | exact superpose eq97 eq208
    | (have j0 := eq208 X0 X1 X2
       grind)
    | exact resolve eq208 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq208
  have eq238 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq207 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq207
    | (have j0 := eq207 X0 X1
       grind)
    | exact resolve eq207 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq243 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq238 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq238 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq238 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq246 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq243 X0 X1
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq243
    | (have j0 := eq243 X0 X1
       grind)
    | exact resolve eq243 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq243
  have eq298 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (M.op X2 (τ (M.op X0 X0)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq120 X0 X1 X2
       have i₂ := eq131 X0
       grind)
    | exact superpose eq131 eq120
    | exact resolve eq120 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq131
  have eq340 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 (τ (M.op (M.op X0 X0) (M.op X0 X0)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq298 X0 X1 (τ (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq177 (M.op X0 X0)
       grind)
    | exact superpose eq177 eq298
    | exact resolve eq298 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq466 : ∀ X0 X1 : G, (τ X0) = (k (τ X0) (M.op X1 (τ (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq174 X0 X1 (τ (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq177 (M.op X0 X0)
       grind)
    | exact superpose eq177 eq174
    | exact resolve eq174 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq177
  have eq783 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq246 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq246
    | exact resolve eq246 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq800 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq246 (σ X0) X1
       grind)
    | exact superpose eq246 eq15
    | (have j1 := eq246 (σ X0) X1
       grind)
    | exact resolve eq15 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq813 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq800 X0 X1
       have i₂ := eq47 X0
       grind)
    | exact superpose eq47 eq800
    | (have j0 := eq800 X0 X1
       grind)
    | exact resolve eq800 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq844 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq783 (τ X1) X0
       grind)
    | exact superpose eq783 eq18
    | (have j1 := eq783 (τ X1) X0
       grind)
    | exact resolve eq18 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq783
  have eq1467 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq161 x X2 X0 X1
       grind)
    | exact superpose eq161 eq30
    | exact resolve eq30 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq1468 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq161 x X2 X0 X1
       grind)
    | exact superpose eq161 eq9
    | exact resolve eq9 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq1556 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1467 X0 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq1468 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq1468 eq1467
    | exact resolve eq1467 eq1468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467 eq1468
  have eq1701 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k (τ (M.op X0 (σ X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26 (M.op X0 (σ X1)) X1
       have i₂ := eq1556 (σ X1) X0
       grind)
    | exact superpose eq1556 eq26
    | exact resolve eq26 eq1556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq5745 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq844 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq844
    | exact resolve eq844 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq5823 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5745 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5745
    | (have j0 := eq5745 X0 X1
       grind)
    | exact resolve eq5745 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5745
  have eq13441 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq813 x y
       grind)
    | exact superpose eq813 eq16
    | (have j1 := eq813 x y
       grind)
    | exact resolve eq16 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813
  have eq16368 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq13441
       have i₂ := eq5823 y x
       grind)
    | exact superpose eq5823 eq13441
    | (have j1 := eq5823 y x
       grind)
    | (have r₁ := eq13441
       have r₂ := eq5823 y x
       grind)
    | exact resolve eq13441 eq5823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16369 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq16368
  have eq16550 : x ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq16369
       grind)
    | exact superpose eq16369 eq12
    | (have j0 := eq12 x x
       grind)
    | exact resolve eq12 eq16369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16551 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq16369
       grind)
    | exact superpose eq16369 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq16369
       grind)
    | exact resolve eq13 eq16369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16369
  have eq16581 : (k x y) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq16551
  have eq16582 : (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq16550
       have r₂ := eq16581
       grind)
    | exact resolve eq16550 eq16581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16550 eq16581
  have eq16588 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq228 x y
       have i₂ := eq16582
       grind)
    | exact superpose eq16582 eq228
    | (have j0 := eq228 x y
       grind)
    | exact resolve eq228 eq16582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq16601 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16588
  have eq16602 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq16601
  have eq16808 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1701 (σ x) y
       have i₂ := eq16602
       grind)
    | exact superpose eq16602 eq1701
    | exact resolve eq1701 eq16602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1701 eq16602
  have eq16848 : x = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16808
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq16808
    | exact resolve eq16808 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16808
  have eq16861 : x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16582
       have i₂ := eq16848
       grind)
    | exact superpose eq16848 eq16582
    | exact resolve eq16582 eq16848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16582 eq16848
  have eq16882 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq16861
  have eq17080 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16882
       grind)
    | exact superpose eq16882 eq16
    | exact resolve eq16 eq16882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17091 : (σ x) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq16882
       grind)
    | exact superpose eq16882 eq12
    | (have r₁ := eq12 x x
       have r₂ := eq16882
       grind)
    | exact resolve eq12 eq16882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17092 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq16882
       grind)
    | exact superpose eq16882 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq16882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16882
  have eq17124 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq17092
       have r₂ := eq47 x
       grind)
    | exact resolve eq17092 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17092
  have eq17125 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq17091
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq17091
    | exact resolve eq17091 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17091
  have eq17128 : (σ (k x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq17124
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq17124
    | exact resolve eq17124 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17124
  have eq17129 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq17128
       have i₂ := eq47 x
       grind)
    | exact superpose eq47 eq17128
    | exact resolve eq17128 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq17128
  have eq17130 : (σ (k x y)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq17129
       have r₂ := eq17125
       grind)
    | exact resolve eq17129 eq17125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17125 eq17129
  have eq17339 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5823 y x
       have i₂ := eq17130
       grind)
    | exact superpose eq17130 eq5823
    | (have j0 := eq5823 y x
       grind)
    | exact resolve eq5823 eq17130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5823 eq17130
  have eq17425 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq17339
       have r₂ := eq17080
       grind)
    | exact resolve eq17339 eq17080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17339
  have eq17645 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq17080
       have i₂ := eq17425
       grind)
    | exact superpose eq17425 eq17080
    | exact resolve eq17080 eq17425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17080 eq17425
  have eq17679 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq17645
  have eq17680 : x = (M.op x x) := by grind
  clear eq17679
  have eq17833 : ∀ X0 : G, x = (k x (σ (M.op X0 (τ (M.op x x))))) := by
    intro X0
    first
    | (have i₁ := eq340 x x
       have i₂ := eq17680
       grind)
    | exact superpose eq17680 eq340
    | exact resolve eq340 eq17680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq17840 : ∀ X0 : G, (τ x) = (k (τ x) (M.op X0 (τ (M.op x x)))) := by
    intro X0
    first
    | (have i₁ := eq466 x x
       have i₂ := eq17680
       grind)
    | exact superpose eq17680 eq466
    | exact resolve eq466 eq17680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq17909 : ∀ X0 : G, (τ x) = (k (τ x) (M.op X0 (τ x))) := by
    intro X0
    first
    | (have i₁ := eq17840 X0
       have i₂ := eq17680
       grind)
    | exact superpose eq17680 eq17840
    | exact resolve eq17840 eq17680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17840
  have eq17912 : ∀ X0 : G, x = (k x (σ (M.op X0 (τ x)))) := by
    intro X0
    first
    | (have i₁ := eq17833 X0
       have i₂ := eq17680
       grind)
    | exact superpose eq17680 eq17833
    | exact resolve eq17833 eq17680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17833
  have eq18404 : ∀ X0 X1 : G, (M.op x x) = (M.op x (σ X1)) ∨ (σ (k (k (τ x) (M.op X0 (τ x))) X1)) = (M.op x (σ X1)) ∨ x = (M.op x (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq237 x (M.op X0 (τ x)) x
       have i₂ := eq17912 X0
       grind)
    | exact superpose eq17912 eq237
    | exact resolve eq237 eq17912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237 eq17912
  have eq18445 : ∀ X0 X1 : G, x = (M.op x (σ X1)) ∨ (σ (k (k (τ x) (M.op X0 (τ x))) X1)) = (M.op x (σ X1)) ∨ x = (M.op x (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18404 X0 X1
       have i₂ := eq17680
       grind)
    | exact superpose eq17680 eq18404
    | (have j0 := eq18404 X0 X1
       grind)
    | exact resolve eq18404 eq17680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18404
  have eq18446 : ∀ X0 X1 : G, x = (M.op x (σ X1)) ∨ (σ (k (k (τ x) (M.op X0 (τ x))) X1)) = (M.op x (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq18445 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18445
  have eq18465 : ∀ X1 : G, (M.op x (σ X1)) = (σ (k (τ x) X1)) ∨ x = (M.op x (σ X1)) := by
    intro X1
    first
    | (have i₁ := eq18446 x X1
       have i₂ := eq17909 x
       grind)
    | exact superpose eq17909 eq18446
    | (have j0 := eq18446 x X1
       grind)
    | exact resolve eq18446 eq17909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17909 eq18446
  have eq18468 : ∀ X1 : G, (k x (σ X1)) = (M.op x (σ X1)) ∨ x = (M.op x (σ X1)) := by
    intro X1
    first
    | (have i₁ := eq18465 X1
       have i₂ := eq17 x X1
       grind)
    | exact superpose eq17 eq18465
    | (have j0 := eq18465 X1
       grind)
    | exact resolve eq18465 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq18465
  have eq18469 : ∀ X1 : G, (k x (σ X1)) = (M.op x (σ X1)) := by
    intro X1
    first
    | (have j0 := eq18468 X1
       have j1 := eq12 x (σ X1)
       grind)
    | (have r₁ := eq18468 X1
       have r₂ := eq12 x (σ X1)
       grind)
    | exact resolve eq18468 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18468
  have eq19012 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq18469 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18469
    | exact resolve eq18469 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18469
  have eq19144 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13441
       have i₂ := eq19012 y
       grind)
    | exact superpose eq19012 eq13441
    | exact resolve eq13441 eq19012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13441
  have eq19206 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq19144
  have eq19227 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19206
       have i₂ := eq17680
       grind)
    | exact superpose eq17680 eq19206
    | exact resolve eq19206 eq17680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17680 eq19206
  have eq19447 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19227
       grind)
    | exact superpose eq19227 eq16
    | exact resolve eq16 eq19227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19478 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1556 (σ y) (σ x)
       have i₂ := eq19227
       grind)
    | exact superpose eq19227 eq1556
    | exact resolve eq1556 eq19227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1556 eq19227
  have eq19496 : (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq19478
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq19478
    | exact resolve eq19478 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19478
  have eq19509 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq19496
       have i₂ := eq19012 y
       grind)
    | exact superpose eq19012 eq19496
    | exact resolve eq19496 eq19012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19012 eq19496
  have eq19522 : False := by grind
  exact eq19522

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyx_x_pyx_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq29 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq58 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq58
    | exact resolve eq58 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq58 (τ X0)
       have i₂ := eq29 X0 X0
       grind)
    | exact superpose eq29 eq58
    | exact resolve eq58 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq60
    | exact resolve eq60 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq62 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq59 X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq59
    | exact resolve eq59 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq59
  have eq66 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq54 (σ X0)
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq54
    | exact resolve eq54 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq68 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op X2 (M.op X1 (σ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X2 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 X2 : G, X1 ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X2 (M.op X0 (M.op X1 X1))) = (k (M.op X2 (M.op X0 (M.op X1 X1))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 (M.op X2 (M.op X0 X0))) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op X2 (M.op X0 (M.op X1 X1))) X1
       grind)
    | (have r₁ := eq13 (M.op X1 (M.op X2 (M.op X0 X0))) X0
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 X1))) = (k (M.op X2 (M.op X0 (M.op X1 X1))) X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq85 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq112 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op X1 (σ (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 (σ (M.op (M.op X0 X0) (M.op X0 X0))) X1
       have i₂ := eq67 (M.op X0 X0)
       grind)
    | exact superpose eq67 eq68
    | exact resolve eq68 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op X3 (M.op (M.op X0 X1) (M.op X0 X1))) (M.op X2 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 (M.op X0 X1) X3 (M.op X2 (M.op X1 X1))
       have i₂ := eq53 X1 X2 X0
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq398 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ (M.op X1 X2) ∨ (M.op X1 X2) = (k X2 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2732 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq398 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq2733 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2732 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2732
  have eq2749 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2733 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2733
    | (have j0 := eq2733 (σ X1) (σ X0)
       grind)
    | exact resolve eq2733 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2826 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq2733 X0 (τ X1)
       grind)
    | exact superpose eq2733 eq17
    | (have j1 := eq2733 X0 (τ X1)
       grind)
    | exact resolve eq17 eq2733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2956 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2826 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2826
    | exact resolve eq2826 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2826
  have eq3013 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2956 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2956
    | (have j0 := eq2956 X0 X1
       grind)
    | exact resolve eq2956 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2956
  have eq3262 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2749 y x
       grind)
    | exact superpose eq2749 eq16
    | (have j1 := eq2749 y x
       grind)
    | exact resolve eq16 eq2749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3276 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2749 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3304 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X1 X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3276 (τ X0) (τ X1)
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq3276
    | (have j0 := eq3276 (τ X0) (τ X1)
       grind)
    | exact resolve eq3276 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3276
  have eq3327 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X1 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3304 X0 X1
       have i₂ := eq11 (k X1 X0)
       grind)
    | exact superpose eq11 eq3304
    | (have j0 := eq3304 X0 X1
       grind)
    | exact resolve eq3304 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3304
  have eq3332 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3327 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3327
    | (have j0 := eq3327 X0 X1
       grind)
    | exact resolve eq3327 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3327
  have eq3334 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X1 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3332 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3332
    | (have j0 := eq3332 X0 X1
       grind)
    | exact resolve eq3332 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3332
  have eq3336 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3334 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3334
    | (have j0 := eq3334 X0 X1
       grind)
    | exact resolve eq3334 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3334
  have eq3518 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3262
       have i₂ := eq3013 y x
       grind)
    | exact superpose eq3013 eq3262
    | (have j1 := eq3013 (σ y) (σ x)
       grind)
    | (have r₁ := eq3262
       have r₂ := eq3013 y x
       grind)
    | exact resolve eq3262 eq3013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3013 eq3262
  have eq3519 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3518
  have eq3588 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq66 x (σ y)
       have i₂ := eq3519
       grind)
    | exact superpose eq3519 eq66
    | exact resolve eq66 eq3519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq3590 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq3519
       grind)
    | exact superpose eq3519 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq3519
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3519
       grind)
    | exact resolve eq13 eq3519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3592 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq3590
  have eq3593 : (σ x) = (σ (M.op x x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3592
       have i₂ := eq62 x
       grind)
    | exact superpose eq62 eq3592
    | exact resolve eq3592 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3592
  have eq3594 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3588
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3588
    | exact resolve eq3588 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3588
  have eq3595 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3593
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3593
    | exact resolve eq3593 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3593
  have eq6484 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq3595
       grind)
    | exact superpose eq3595 eq10
    | exact resolve eq10 eq3595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3595
  have eq6555 : (σ x) = (σ (M.op x x)) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6484
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq6484
    | exact resolve eq6484 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6484
  have eq6556 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3594
       have i₂ := eq6555
       grind)
    | exact superpose eq6555 eq3594
    | (have r₁ := eq3594
       have r₂ := eq6555
       grind)
    | exact resolve eq3594 eq6555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6555
  have eq6612 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (k y x) := by grind
  clear eq6556
  have eq6613 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (k y x) := by grind
  clear eq6612
  have eq6722 : (k y x) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq6613
       grind)
    | exact superpose eq6613 eq10
    | exact resolve eq10 eq6613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6613
  have eq6796 : y = (k y x) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq6722
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6722
    | exact resolve eq6722 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6722
  have eq6799 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6796
       have i₂ := eq2733 x y
       grind)
    | exact superpose eq2733 eq6796
    | (have j1 := eq2733 x y
       grind)
    | exact resolve eq6796 eq2733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2733 eq6796
  have eq6854 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq6799
  have eq30532 : ∀ X0 X1 X3 : G, (M.op X3 (M.op X1 (M.op (M.op X0 X3) (M.op X0 X3)))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 X3 (M.op X1 (M.op (M.op X0 X3) (M.op X0 X3))) x
       have i₂ := eq152 X0 X3 x X1
       grind)
    | exact superpose eq152 eq9
    | exact resolve eq9 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30734 : ∀ X0 X2 : G, (M.op X0 X2) = (M.op (M.op X0 X2) (M.op X0 X2)) ∨ (k X2 (M.op X0 X2)) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq90 x (M.op X0 x) x
       have i₂ := eq30532 X0 x x
       grind)
    | exact superpose eq30532 eq90
    | (have j0 := eq90 X0 (M.op X0 X2) X2
       grind)
    | exact resolve eq90 eq30532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq30735 : ∀ X0 X2 : G, (M.op X0 X2) = (M.op (M.op X0 X2) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq9 (M.op X0 X2) X2 x
       have i₂ := eq30532 X0 x X2
       grind)
    | exact superpose eq30532 eq9
    | exact resolve eq9 eq30532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30736 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X2 X1
       have i₂ := eq30532 X0 (M.op (M.op X0 X1) (M.op X0 X1)) X1
       grind)
    | exact superpose eq30532 eq9
    | exact resolve eq9 eq30532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30836 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30735 (σ X1) (σ X0)
       have i₂ := eq2749 X0 X1
       grind)
    | exact superpose eq2749 eq30735
    | (have j1 := eq2749 X0 (k X0 X1)
       grind)
    | exact resolve eq30735 eq2749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2749
  have eq30871 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30735 x y
       have i₂ := eq6854
       grind)
    | exact superpose eq6854 eq30735
    | exact resolve eq30735 eq6854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6854 eq30735
  have eq30929 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X1 (σ y)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq68 y X1 X0
       have i₂ := eq30871
       grind)
    | exact superpose eq30871 eq68
    | exact resolve eq68 eq30871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30871
  have eq44326 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq30929 X0 (σ x)
       have i₂ := eq3519
       grind)
    | exact superpose eq3519 eq30929
    | exact resolve eq30929 eq3519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30929
  have eq44385 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq44326 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44326
  have eq44398 : (σ y) = (M.op (σ y) (σ (M.op x x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44385 (σ (M.op x x))
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq44385
    | exact resolve eq44385 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq44385
  have eq44434 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq68 x (σ y) X0
       have i₂ := eq44398
       grind)
    | exact superpose eq44398 eq68
    | exact resolve eq68 eq44398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44398
  have eq44456 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44434 (σ x)
       have i₂ := eq3519
       grind)
    | exact superpose eq3519 eq44434
    | exact resolve eq44434 eq3519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3519 eq44434
  have eq44484 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq44456
  have eq44488 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44484
       have i₂ := eq62 x
       grind)
    | exact superpose eq62 eq44484
    | exact resolve eq44484 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44484
  have eq44491 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3594
       have i₂ := eq44488
       grind)
    | exact superpose eq44488 eq3594
    | (have r₁ := eq3594
       have r₂ := eq44488
       grind)
    | exact resolve eq3594 eq44488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3594 eq44488
  have eq44567 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
  clear eq44491
  have eq44568 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
  clear eq44567
  have eq44714 : (k y x) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq44568
       grind)
    | exact superpose eq44568 eq10
    | exact resolve eq10 eq44568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44568
  have eq44814 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44714
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq44714
    | exact resolve eq44714 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44714
  have eq45069 : x ≠ x ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3336 x y
       have i₂ := eq44814
       grind)
    | exact superpose eq44814 eq3336
    | (have j0 := eq3336 x y
       grind)
    | (have r₁ := eq3336 x y
       have r₂ := eq44814
       grind)
    | exact resolve eq3336 eq44814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3336 eq44814
  have eq45095 : x ≠ x ∨ x = (M.op x y) := by grind
  clear eq45069
  have eq45096 : x = (M.op x y) := by grind
  clear eq45095
  have eq45170 : x ≠ (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq45096
       grind)
    | exact superpose eq45096 eq12
    | exact resolve eq12 eq45096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45172 : ∀ X0 : G, (M.op X0 (M.op y y)) = (M.op (M.op X0 (M.op y y)) x) := by
    intro X0
    first
    | (have i₁ := eq53 y X0 x
       have i₂ := eq45096
       grind)
    | exact superpose eq45096 eq53
    | exact resolve eq53 eq45096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45173 : ∀ X0 X1 : G, (M.op X0 (M.op x x)) = (M.op (M.op X0 (M.op x x)) (M.op X1 (M.op y y))) := by
    intro X0 X1
    first
    | (have i₁ := eq152 x y x x
       have i₂ := eq45096
       grind)
    | exact superpose eq45096 eq152
    | exact resolve eq152 eq45096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50145 : ∀ X0 X1 : G, (M.op y y) = (M.op (M.op y y) (M.op X1 (M.op X0 (M.op x x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op y y) X1 (M.op X0 (M.op x x))
       have i₂ := eq45173 X0 (M.op y y)
       grind)
    | exact superpose eq45173 eq9
    | exact resolve eq9 eq45173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45173
  have eq50221 : ∀ X0 X1 : G, (M.op y y) = (M.op (M.op y y) (M.op X1 (M.op (M.op X0 x) (M.op X0 x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq50145 x (M.op X1 (M.op (M.op X0 x) (M.op X0 x)))
       have i₂ := eq152 X0 x x X1
       grind)
    | exact superpose eq152 eq50145
    | exact resolve eq50145 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50145
  have eq53041 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 x) (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq30532 (M.op X0 x) (M.op y y) (M.op X0 x)
       have i₂ := eq50221 X0 (M.op (M.op X0 x) (M.op X0 x))
       grind)
    | exact superpose eq50221 eq30532
    | exact resolve eq30532 eq50221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50221
  have eq53082 : ∀ X0 X1 : G, y = (M.op y (M.op X1 (M.op X0 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 y X1 (M.op X0 x)
       have i₂ := eq53041 X0
       grind)
    | exact superpose eq53041 eq9
    | exact resolve eq9 eq53041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53083 : ∀ X0 X1 : G, (M.op X1 x) = (M.op (M.op X1 x) (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 y (M.op X0 x) x
       have i₂ := eq53041 X0
       grind)
    | exact superpose eq53041 eq53
    | exact resolve eq53 eq53041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53041
  have eq53177 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 x)) = (M.op (M.op X1 (M.op X0 x)) (M.op X2 (M.op y y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30532 y X1 (M.op X1 (M.op X0 x))
       have i₂ := eq53082 X0 X1
       grind)
    | exact superpose eq53082 eq30532
    | exact resolve eq30532 eq53082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53082
  have eq56671 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 x)) = (M.op (M.op X2 (M.op X1 x)) (M.op X0 x)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53177 X1 X2 (M.op X0 x)
       have i₂ := eq53083 y X0
       grind)
    | exact superpose eq53083 eq53177
    | exact resolve eq53177 eq53083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53083 eq53177
  have eq56769 : ∀ X0 X1 X2 : G, x = (M.op x (M.op X2 (M.op X0 (M.op X1 x)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 x X2 (M.op X0 (M.op X1 x))
       have i₂ := eq56671 x X1 X0
       grind)
    | exact superpose eq56671 eq9
    | exact resolve eq9 eq56671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56671
  have eq56807 : ∀ X0 X1 X2 : G, x = (M.op x (M.op X1 (M.op X2 (M.op X0 (M.op y y))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56769 X2 (M.op X0 (M.op y y)) X1
       have i₂ := eq45172 X0
       grind)
    | exact superpose eq45172 eq56769
    | exact resolve eq56769 eq45172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45172
  have eq56953 : ∀ X0 X1 X3 : G, x = (M.op x (M.op X3 (M.op X1 (M.op (M.op X0 y) (M.op X0 y))))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq56807 x X3 (M.op X1 (M.op (M.op X0 y) (M.op X0 y)))
       have i₂ := eq152 X0 y x X1
       grind)
    | exact superpose eq152 eq56807
    | exact resolve eq56807 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56807
  have eq57324 : ∀ X0 X1 X3 : G, x = (M.op x (M.op X1 (M.op (M.op X0 (M.op X3 y)) (M.op X0 (M.op X3 y))))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq56953 X3 x (M.op X1 (M.op (M.op X0 (M.op X3 y)) (M.op X0 (M.op X3 y))))
       have i₂ := eq152 X0 (M.op X3 y) x X1
       grind)
    | exact superpose eq152 eq56953
    | exact resolve eq56953 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56953
  have eq58279 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op X0 (M.op X1 y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq30532 (M.op X0 (M.op X1 y)) x (M.op X0 (M.op X1 y))
       have i₂ := eq57324 X0 (M.op (M.op X0 (M.op X1 y)) (M.op X0 (M.op X1 y))) X1
       grind)
    | exact superpose eq57324 eq30532
    | exact resolve eq30532 eq57324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57324
  have eq58348 : ∀ X0 X1 X2 X3 : G, x = (M.op x (M.op X2 (M.op X3 (M.op X0 (M.op X1 y))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56769 X3 (M.op X0 (M.op X1 y)) X2
       have i₂ := eq58279 X0 X1
       grind)
    | exact superpose eq58279 eq56769
    | exact resolve eq56769 eq58279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56769
  have eq61449 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X1 X0))) = X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30532 X1 X2 X0
       have i₂ := eq30734 X1 X0
       grind)
    | exact superpose eq30734 eq30532
    | (have j1 := eq30734 X1 X0
       grind)
    | exact resolve eq30532 eq30734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30734
  have eq62226 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X1 X1))) = X1 ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq152 X1 X0 X2 X0
       have i₂ := eq61449 X0 X1 (M.op X1 X0)
       grind)
    | exact superpose eq61449 eq152
    | (have j1 := eq61449 X1 X1 X2
       grind)
    | exact resolve eq152 eq61449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq61449
  have eq64973 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X2 X0)) ∨ (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X2 X0
       have i₂ := eq62226 X1 X0 (M.op X0 X0)
       grind)
    | exact superpose eq62226 eq9
    | (have j1 := eq62226 X1 X0 X2
       grind)
    | exact resolve eq9 eq62226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62226
  have eq86250 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op X2 (σ (M.op X0 X0)))) ∨ (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq112 X0 X2
       have i₂ := eq64973 X0 X1 X0
       grind)
    | exact superpose eq64973 eq112
    | (have j1 := eq64973 X0 X1 X2
       grind)
    | exact resolve eq112 eq64973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq64973
  have eq239760 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 (M.op X0 X1)) (M.op X2 (M.op X0 X1)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30532 X0 (M.op (M.op X2 (M.op X0 X1)) (M.op X2 (M.op X0 X1))) X1
       have i₂ := eq30736 X2 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq30736 eq30532
    | exact resolve eq30532 eq30736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30532 eq30736
  have eq240593 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 (M.op X2 (M.op X0 X1)) X1 X2
       have i₂ := eq239760 X0 X1 X2
       grind)
    | exact superpose eq239760 eq53
    | exact resolve eq53 eq239760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq239760
  have eq286474 : ∀ X1 X2 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k X1 (M.op X2 X1)) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq68 X1 x (σ X1)
       have i₂ := eq86250 X1 X2 x
       grind)
    | exact superpose eq86250 eq68
    | (have j1 := eq86250 X1 X2 X2
       grind)
    | exact resolve eq68 eq86250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq86250
  have eq286701 : ∀ X1 X2 : G, (k X1 (M.op X2 X1)) = X1 ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X1 X2
    first
    | (have i₁ := eq286474 X1 X2
       have i₂ := eq62 X1
       grind)
    | exact superpose eq62 eq286474
    | (have j0 := eq286474 X1 X2
       grind)
    | exact resolve eq286474 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286474
  have eq287402 : ∀ X0 X1 : G, (σ (τ X1)) = (k X1 (σ (M.op X0 (τ X1)))) ∨ (σ (τ X1)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (M.op X0 (τ X1))
       have i₂ := eq286701 (τ X1) X0
       grind)
    | exact superpose eq286701 eq17
    | (have j1 := eq286701 (τ X1) x
       grind)
    | exact resolve eq17 eq286701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq286701
  have eq287646 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 (τ X1)))) = X1 ∨ (σ (τ X1)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq287402 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq287402
    | (have j0 := eq287402 X0 X1
       grind)
    | exact resolve eq287402 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287402
  have eq287814 : ∀ X0 X1 : G, (σ (τ X1)) = (σ (τ (M.op X1 X1))) ∨ (k X1 (σ (M.op X0 (τ X1)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq287646 X0 X1
       have i₂ := eq61 X1
       grind)
    | exact superpose eq61 eq287646
    | (have j0 := eq287646 X0 X1
       grind)
    | exact resolve eq287646 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq287646
  have eq287930 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ X1)) ∨ (k X1 (σ (M.op X0 (τ X1)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq287814 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq287814
    | (have j0 := eq287814 X0 X1
       grind)
    | exact resolve eq287814 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287814
  have eq288000 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 (τ X1)))) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq287930 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq287930
    | (have j0 := eq287930 X0 X1
       grind)
    | exact resolve eq287930 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287930
  have eq288079 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ (M.op X1 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq288000 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq288000
    | (have j0 := eq288000 X0 (σ X0)
       grind)
    | exact resolve eq288000 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288000
  have eq288641 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (M.op X1 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq288079 X0 X1
       have i₂ := eq15 X0 (M.op X1 X0)
       grind)
    | exact superpose eq15 eq288079
    | (have j0 := eq288079 X0 X1
       grind)
    | exact resolve eq288079 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288079
  have eq288683 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (M.op X1 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq288641 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq288641
    | (have j0 := eq288641 X0 X1
       grind)
    | exact resolve eq288641 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288641
  have eq291131 : (σ y) = (σ (k y x)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq288683 y x
       have i₂ := eq45096
       grind)
    | exact superpose eq45096 eq288683
    | (have j0 := eq288683 y x
       grind)
    | exact resolve eq288683 eq45096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288683
  have eq472866 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq30836 y x
       have i₂ := eq291131
       grind)
    | exact superpose eq291131 eq30836
    | (have j0 := eq30836 y y
       grind)
    | exact resolve eq30836 eq291131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291131
  have eq473485 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq472866
       have i₂ := eq62 y
       grind)
    | exact superpose eq62 eq472866
    | exact resolve eq472866 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq472866
  have eq473486 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq473485
  have eq476488 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq473486
       grind)
    | exact superpose eq473486 eq16
    | exact resolve eq16 eq473486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473486
  have eq476646 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq476488
       have i₂ := eq45096
       grind)
    | exact superpose eq45096 eq476488
    | exact resolve eq476488 eq45096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476488
  have eq476647 : (σ y) = (σ (M.op y y)) := by grind
  clear eq476646
  have eq476701 : (τ (σ y)) = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq476647
       grind)
    | exact superpose eq476647 eq10
    | exact resolve eq10 eq476647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476647
  have eq476872 : y = (M.op y y) := by
    first
    | (have i₁ := eq476701
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq476701
    | exact resolve eq476701 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476701
  have eq477420 : ∀ X0 X1 : G, y = (M.op y (M.op X1 (M.op X0 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq240593 X0 y y X1
       have i₂ := eq476872
       grind)
    | exact superpose eq476872 eq240593
    | exact resolve eq240593 eq476872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240593 eq476872
  have eq478251 : ∀ X2 : G, x = (M.op x (M.op X2 y)) := by
    intro X2
    first
    | (have i₁ := eq58348 x x X2 y
       have i₂ := eq477420 x x
       grind)
    | exact superpose eq477420 eq58348
    | exact resolve eq58348 eq477420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58348 eq477420
  have eq479047 : x = (M.op x x) := by
    first
    | (have i₁ := eq58279 x x
       have i₂ := eq478251 x
       grind)
    | exact superpose eq478251 eq58279
    | exact resolve eq58279 eq478251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58279 eq478251
  have eq479218 : x ≠ x ∨ x = (k y x) := by
    first
    | (have i₁ := eq45170
       have i₂ := eq479047
       grind)
    | exact superpose eq479047 eq45170
    | (have r₁ := eq45170
       have r₂ := eq479047
       grind)
    | exact resolve eq45170 eq479047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45170 eq479047
  have eq479670 : x = (k y x) := by grind
  clear eq479218
  have eq482189 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30836 y x
       have i₂ := eq479670
       grind)
    | exact superpose eq479670 eq30836
    | (have j0 := eq30836 y x
       grind)
    | exact resolve eq30836 eq479670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30836 eq479670
  have eq482196 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq482189
  have eq482498 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq482196
       grind)
    | exact superpose eq482196 eq16
    | exact resolve eq16 eq482196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482196
  have eq482628 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq482498
       have i₂ := eq45096
       grind)
    | exact superpose eq45096 eq482498
    | exact resolve eq482498 eq45096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45096 eq482498
  have eq482629 : False := by grind
  exact eq482629

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pxx_pxx_pyx_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq20 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq28 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X0 X0))) ≠ X0 ∨ (M.op (M.op X1 (M.op X2 (M.op X0 X0))) (M.op X1 (M.op X2 (M.op X0 X0)))) = (k (M.op X1 (M.op X2 (M.op X0 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 (M.op X2 (M.op X0 X0))) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X1 (M.op X2 (M.op X0 X0))) X0
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq47 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq77 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  have eq82 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq93 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq20 X1 X0 X3
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq106 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq47 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq153 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq82 x y
       grind)
    | exact superpose eq82 eq16
    | (have j1 := eq82 x y
       grind)
    | exact resolve eq16 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq335 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq87 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq87
    | exact resolve eq87 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq366 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq335 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq335
    | (have j0 := eq335 X0 X1
       grind)
    | exact resolve eq335 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq777 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq153
       have i₂ := eq366 x y
       grind)
    | exact superpose eq366 eq153
    | (have j1 := eq366 (σ x) (σ y)
       grind)
    | (have r₁ := eq153
       have r₂ := eq366 x y
       grind)
    | (have r₁ := eq153
       have r₂ := eq366 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq153
       have r₂ := eq366 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq153 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq778 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq777
  have eq1036 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq93 x X2 X0 X1
       grind)
    | exact superpose eq93 eq9
    | exact resolve eq9 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq1061 : ∀ X0 X2 : G, (M.op X2 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op X2 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq28 (M.op x X2) X2 X0
       have i₂ := eq1036 X0 x X2
       grind)
    | exact superpose eq1036 eq28
    | exact resolve eq28 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1062 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq1036 x X1 X0
       grind)
    | exact superpose eq1036 eq9
    | exact resolve eq9 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq2401 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1061 (τ X0) (τ X0)
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq1061
    | (have j1 := eq77 X0
       grind)
    | (have r₁ := eq1061 (τ X0) (τ X0)
       have r₂ := eq77 X0
       grind)
    | exact resolve eq1061 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061
  have eq2403 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq77 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq2404 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq2401 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2401
  have eq2407 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2404 X0
       have i₂ := eq38 X0 X0
       grind)
    | exact superpose eq38 eq2404
    | (have j0 := eq2404 X0
       grind)
    | exact resolve eq2404 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq2404
  have eq2415 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq2407 X0
       have j1 := eq2403 X0
       grind)
    | (have r₁ := eq2407 X0
       have r₂ := eq2403 X0
       grind)
    | exact resolve eq2407 eq2403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2403 eq2407
  have eq2482 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2415 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2415
    | exact resolve eq2415 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2415
  have eq2527 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq2482 X0
       have i₂ := eq27 (σ X0) X0
       grind)
    | exact superpose eq27 eq2482
    | exact resolve eq2482 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2482
  have eq2531 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2527 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2527
    | exact resolve eq2527 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2527
  have eq2537 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq106 X0
       have i₂ := eq2531 X0
       grind)
    | exact superpose eq2531 eq106
    | (have j0 := eq106 X0
       grind)
    | exact resolve eq106 eq2531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq2559 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq2531 (σ X0)
       grind)
    | exact superpose eq2531 eq15
    | exact resolve eq15 eq2531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2583 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2559 X0
       have i₂ := eq2531 X0
       grind)
    | exact superpose eq2531 eq2559
    | exact resolve eq2559 eq2531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2531 eq2559
  have eq2884 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1062 (σ X0) (σ X0)
       have i₂ := eq2583 X0
       grind)
    | exact superpose eq2583 eq1062
    | exact resolve eq1062 eq2583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61696 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq778
       grind)
    | exact superpose eq778 eq16
    | exact resolve eq16 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq61697 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq61696
       have r₂ := eq2583 x
       grind)
    | exact resolve eq61696 eq2583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61696
  have eq62233 : y ≠ y ∨ (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq61697
       grind)
    | exact superpose eq61697 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq61697
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq61697
       grind)
    | exact resolve eq12 eq61697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62240 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1062 y x
       have i₂ := eq61697
       grind)
    | exact superpose eq61697 eq1062
    | exact resolve eq1062 eq61697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61697
  have eq62256 : (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq62233
  have eq62272 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1062 (σ y) (σ x)
       have i₂ := eq62240
       grind)
    | exact superpose eq62240 eq1062
    | exact resolve eq1062 eq62240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062 eq62240
  have eq62290 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq62272
       have i₂ := eq2583 y
       grind)
    | exact superpose eq2583 eq62272
    | exact resolve eq62272 eq2583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62272
  have eq62681 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq62290
       grind)
    | exact superpose eq62290 eq10
    | exact resolve eq10 eq62290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62290
  have eq62806 : x = y ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq62681
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq62681
    | exact resolve eq62681 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62681
  have eq63092 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq62806
       grind)
    | exact superpose eq62806 eq16
    | exact resolve eq16 eq62806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62806
  have eq63093 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq63092
       have r₂ := eq2583 x
       grind)
    | exact resolve eq63092 eq2583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63092
  have eq63112 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2884 y
       have i₂ := eq63093
       grind)
    | exact superpose eq63093 eq2884
    | exact resolve eq2884 eq63093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2884 eq63093
  have eq63174 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq2537 y
       grind)
    | (have r₁ := eq63112
       have r₂ := eq2537 y
       grind)
    | exact resolve eq63112 eq2537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2537 eq63112
  have eq63184 : (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq63174
       have i₂ := eq2583 y
       grind)
    | exact superpose eq2583 eq63174
    | exact resolve eq63174 eq2583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63174
  have eq169081 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq156 x y
       have i₂ := eq62256
       grind)
    | exact superpose eq62256 eq156
    | (have j0 := eq156 x y
       grind)
    | exact resolve eq156 eq62256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156 eq62256
  have eq169096 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq169081
  have eq169105 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq169096
       have r₂ := eq63184
       grind)
    | exact resolve eq169096 eq63184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169096
  have eq169893 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq169105
       grind)
    | exact superpose eq169105 eq16
    | exact resolve eq16 eq169105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169930 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq169105
       grind)
    | exact superpose eq169105 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq169105
       grind)
    | exact resolve eq12 eq169105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169105
  have eq169958 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq169930
  have eq169966 : (σ (k y x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq169958
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq169958
    | exact resolve eq169958 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169958
  have eq169983 : (σ (k y x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq169966
       have i₂ := eq2583 y
       grind)
    | exact superpose eq2583 eq169966
    | exact resolve eq169966 eq2583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169966
  have eq169989 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq169983
       have i₂ := eq63184
       grind)
    | exact superpose eq63184 eq169983
    | exact resolve eq169983 eq63184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63184 eq169983
  have eq171047 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq366 x y
       have i₂ := eq169989
       grind)
    | exact superpose eq169989 eq366
    | (have j0 := eq366 x y
       grind)
    | exact resolve eq366 eq169989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366 eq169989
  have eq171305 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq171047
       have r₂ := eq169893
       grind)
    | exact resolve eq171047 eq169893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171047
  have eq172037 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq169893
       have i₂ := eq171305
       grind)
    | exact superpose eq171305 eq169893
    | exact resolve eq169893 eq171305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169893 eq171305
  have eq172153 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq172037
  have eq172154 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq172153
  have eq173046 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq172154
       grind)
    | exact superpose eq172154 eq10
    | exact resolve eq10 eq172154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172154
  have eq173314 : x = y ∨ x = y := by
    first
    | (have i₁ := eq173046
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq173046
    | exact resolve eq173046 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173046
  have eq173315 : x = y := by grind
  clear eq173314
  have eq173374 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq173315
       grind)
    | exact superpose eq173315 eq16
    | exact resolve eq16 eq173315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173315
  have eq173573 : False := by grind
  exact eq173573

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_pyy_pyx_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq17
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq74 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq26
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq26 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq80 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq19 X1 X0 X3
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq105 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq69 x y
       grind)
    | exact superpose eq69 eq16
    | (have j1 := eq69 x y
       grind)
    | exact resolve eq16 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq69 X0 X0
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq69 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq69 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq69 X0 X1
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq69 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq114 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq113 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq118 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq107 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq121 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq118 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq118 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq118 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq627 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq80 x X2 X0 X1
       grind)
    | exact superpose eq80 eq9
    | exact resolve eq9 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq653 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq627 x X1 X0
       grind)
    | exact superpose eq627 eq9
    | exact resolve eq9 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq692 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq105
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq105
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq105 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq693 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq692
  have eq4482 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (τ (σ X0)) X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq74 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq4483 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (τ (σ X0)) X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq4482 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4482
  have eq4486 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4483 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4483
    | (have j0 := eq4483 X0
       grind)
    | exact resolve eq4483 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4483
  have eq4488 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4486 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4486
    | exact resolve eq4486 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4486
  have eq4550 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4488 X0
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq4488
    | (have j0 := eq4488 X0
       grind)
    | exact resolve eq4488 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq4488
  have eq4568 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq4550 X0
       grind)
    | exact superpose eq4550 eq11
    | (have j1 := eq4550 X0
       grind)
    | exact resolve eq11 eq4550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4550
  have eq4640 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4568 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4568
    | (have j0 := eq4568 X0
       grind)
    | exact resolve eq4568 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4568
  have eq4654 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4640 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq4640 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq4640 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4640
  have eq4730 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq114 X0
       have i₂ := eq4654 X0
       grind)
    | exact superpose eq4654 eq114
    | (have j0 := eq114 X0
       grind)
    | exact resolve eq114 eq4654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq4734 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq121 X0 X1
       have i₂ := eq4654 X0
       grind)
    | exact superpose eq4654 eq121
    | (have j0 := eq121 X0 X1
       grind)
    | exact resolve eq121 eq4654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq4768 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4654 (σ X0)
       grind)
    | exact superpose eq4654 eq15
    | exact resolve eq15 eq4654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4824 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4768 X0
       have i₂ := eq4654 X0
       grind)
    | exact superpose eq4654 eq4768
    | exact resolve eq4768 eq4654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4654 eq4768
  have eq5223 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq653 (σ X0) (σ X0)
       have i₂ := eq4824 X0
       grind)
    | exact superpose eq4824 eq653
    | exact resolve eq653 eq4824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7435 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq653 x y
       have i₂ := eq693
       grind)
    | exact superpose eq693 eq653
    | exact resolve eq653 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq7449 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq7435
  have eq7467 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq7449
       have i₂ := eq4824 x
       grind)
    | exact superpose eq4824 eq7449
    | exact resolve eq7449 eq4824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7449
  have eq13131 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq653 (σ x) (σ y)
       have i₂ := eq7467
       grind)
    | exact superpose eq7467 eq653
    | exact resolve eq653 eq7467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653 eq7467
  have eq13147 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq4730 x
       grind)
    | (have r₁ := eq13131
       have r₂ := eq4730 x
       grind)
    | exact resolve eq13131 eq4730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13131
  have eq13159 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13147
       have i₂ := eq4824 x
       grind)
    | exact superpose eq4824 eq13147
    | exact resolve eq13147 eq4824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13147
  have eq13187 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq4734 x X0
       have i₂ := eq13159
       grind)
    | exact superpose eq13159 eq4734
    | (have j0 := eq4734 x X0
       grind)
    | (have r₁ := eq4734 x x
       have r₂ := eq13159
       grind)
    | exact resolve eq4734 eq13159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13194 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5223 x
       have i₂ := eq13159
       grind)
    | exact superpose eq13159 eq5223
    | exact resolve eq5223 eq13159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5223 eq13159
  have eq13229 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq13187 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13187
  have eq13236 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq4730 x
       grind)
    | (have r₁ := eq13194
       have r₂ := eq4730 x
       grind)
    | exact resolve eq13194 eq4730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4730 eq13194
  have eq13239 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq13229 X0
       have j1 := eq4734 x X0
       grind)
    | (have r₁ := eq13229 X0
       have r₂ := eq4734 x x
       grind)
    | exact resolve eq13229 eq4734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4734 eq13229
  have eq13245 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13236
       have i₂ := eq4824 x
       grind)
    | exact superpose eq4824 eq13236
    | exact resolve eq13236 eq4824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4824 eq13236
  have eq13569 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq13245
       grind)
    | exact superpose eq13245 eq10
    | exact resolve eq10 eq13245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13245
  have eq13666 : x = (M.op x x) := by
    first
    | (have i₁ := eq13569
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq13569
    | exact resolve eq13569 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13569
  have eq13685 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq13666
       grind)
    | exact superpose eq13666 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq13666
       grind)
    | exact resolve eq12 eq13666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13666
  have eq13742 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq13685 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13685
  have eq14119 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq13239 (σ X0)
       grind)
    | exact superpose eq13239 eq15
    | exact resolve eq15 eq13239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13239
  have eq14165 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq14119 X0
       have i₂ := eq13742 X0
       grind)
    | exact superpose eq13742 eq14119
    | exact resolve eq14119 eq13742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13742 eq14119
  have eq15140 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14165 y
       grind)
    | exact superpose eq14165 eq16
    | (have r₁ := eq16
       have r₂ := eq14165 y
       grind)
    | exact resolve eq16 eq14165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14165
  have eq15227 : False := by grind
  exact eq15227

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_y_pyx_Equation446 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law446 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq109 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq110 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq110
    | exact resolve eq110 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq193 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
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
  clear eq20
  have eq194 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq201 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq194 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq194
    | (have j0 := eq194 X0 X1
       grind)
    | exact resolve eq194 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq213 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq109 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq109 X1 X0 X3
       grind)
    | exact superpose eq109 eq109
    | exact resolve eq109 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq713 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq201 x y
       grind)
    | exact superpose eq201 eq16
    | (have j1 := eq201 x y
       grind)
    | exact resolve eq16 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq1825 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq193 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq193
    | exact resolve eq193 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq1887 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1825 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1825
    | (have j0 := eq1825 X0 X1
       grind)
    | exact resolve eq1825 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1825
  have eq2272 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq713
       have i₂ := eq1887 x y
       grind)
    | exact superpose eq1887 eq713
    | (have j1 := eq1887 x y
       grind)
    | (have r₁ := eq713
       have r₂ := eq1887 x y
       grind)
    | (have r₁ := eq713
       have r₂ := eq1887 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq713
       have r₂ := eq1887 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq713 eq1887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713 eq1887
  have eq2273 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq2272
  have eq7367 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq213 x X2 X0 X1
       grind)
    | exact superpose eq213 eq9
    | exact resolve eq9 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq7442 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq7367 x X1 X0
       grind)
    | exact superpose eq7367 eq9
    | exact resolve eq9 eq7367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7367
  have eq9444 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2273
       grind)
    | exact superpose eq2273 eq16
    | exact resolve eq16 eq2273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2273
  have eq9445 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq9444
       have r₂ := eq23 x
       grind)
    | exact resolve eq9444 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9444
  have eq9447 : y = (τ (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq9445
       grind)
    | exact superpose eq9445 eq10
    | exact resolve eq10 eq9445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9445
  have eq9501 : x = y ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9447
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9447
    | exact resolve eq9447 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9447
  have eq9503 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9501
       grind)
    | exact superpose eq9501 eq16
    | exact resolve eq16 eq9501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9501
  have eq9504 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq9503
       have r₂ := eq23 x
       grind)
    | exact resolve eq9503 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq9503
  have eq9520 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq9504
       grind)
    | exact superpose eq9504 eq10
    | exact resolve eq10 eq9504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9504
  have eq9574 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9520
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9520
    | exact resolve eq9520 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9520
  have eq9575 : x = (M.op y y) := by grind
  clear eq9574
  have eq9585 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq111 y
       have i₂ := eq9575
       grind)
    | exact superpose eq9575 eq111
    | exact resolve eq111 eq9575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq9636 : x = (M.op x y) := by
    first
    | (have i₁ := eq7442 y y
       have i₂ := eq9575
       grind)
    | exact superpose eq9575 eq7442
    | exact resolve eq7442 eq9575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7442 eq9575
  have eq9690 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9585
       grind)
    | exact superpose eq9585 eq16
    | exact resolve eq16 eq9585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9585
  have eq9722 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq9690
       have i₂ := eq9636
       grind)
    | exact superpose eq9636 eq9690
    | exact resolve eq9690 eq9636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9636 eq9690
  have eq9723 : False := by grind
  exact eq9723

/-- `Equation4494`: `x ◇ (y ◇ y) = (z ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxx_x_pxy_Equation4494 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4494 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4494.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = a :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
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
  clear eq36
  have eq50 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq44 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq44
    | (have j0 := eq44 y
       grind)
    | exact resolve eq44 eq24
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
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq132 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq178 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X1)) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 (M.op x X1)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op X0 (M.op y y)) = (M.op (M.op x y) y) := by
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
  have eq180 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq16 X2 X1 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (M.op X1 y) y) := by
    intro X1
    first
    | (have i₁ := eq16 x y X1
       have i₂ := eq179 x
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op y y) (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op y y) x
       have i₂ := eq179 (M.op x (M.op y y))
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq191 X0
       have i₂ := eq179 (M.op y y)
       grind)
    | exact superpose eq179 eq191
    | exact resolve eq191 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq199 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op X1 (σ y)) (σ y)) := by
    intro X1
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X0 (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) := by
    intro X0
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq180 eq203
    | exact resolve eq203 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq419 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq704 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1) x
       have i₂ := eq181 (M.op x (M.op X1 X1)) X1 X0
       grind)
    | (have i₁ := eq16 X2 (M.op X1 X1) x
       have i₂ := eq181 X0 X1 (M.op x (M.op X1 X1))
       grind)
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq705 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (k (M.op X1 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq704 X0 X1 X2
       have i₂ := eq184 X1
       grind)
    | exact superpose eq184 eq704
    | exact resolve eq704 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq809 : (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = (k (M.op (M.op x y) y) (M.op y y)) := by
    first
    | (have i₁ := eq184 (M.op y y)
       have i₂ := eq179 (M.op y y)
       grind)
    | exact superpose eq179 eq184
    | exact resolve eq184 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq811 : (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq180 eq184
    | exact resolve eq184 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq821 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X1 X0 (M.op X0 X0)
       have i₂ := eq184 X0
       grind)
    | exact superpose eq184 eq178
    | exact resolve eq178 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq823 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq181 (M.op X0 X0) X0 X1
       have i₂ := eq184 X0
       grind)
    | exact superpose eq184 eq181
    | exact resolve eq181 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq824 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 X0) X0 X1
       have i₂ := eq184 X0
       grind)
    | exact superpose eq184 eq16
    | exact resolve eq16 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq825 : (M.op (M.op x y) y) = (k (M.op y y) y) := by
    first
    | (have i₁ := eq179 (M.op y y)
       have i₂ := eq184 y
       grind)
    | exact superpose eq184 eq179
    | exact resolve eq179 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq826 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ y) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq180 (M.op sF3 sF3)
       have i₂ := eq184 sF3
       grind)
    | exact superpose eq184 eq180
    | exact resolve eq180 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq835 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq204 eq811
    | exact resolve eq811 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq837 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) (M.op y y)) := by
    first
    | exact superpose eq192 eq809
    | exact resolve eq809 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq839 : (k (σ (M.op y y)) (σ y)) = (σ (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq40 (M.op y y)
       have i₂ := eq825
       grind)
    | exact superpose eq825 eq40
    | exact resolve eq40 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq840 : (k (τ (M.op (σ y) (σ y))) y) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq826 eq152
    | exact resolve eq152 eq826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq1012 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = X0 ∨ (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | exact superpose eq192 eq12
    | (have j0 := eq12 X0 (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op x y) y)
       have r₂ := eq192 X0
       grind)
    | exact resolve eq12 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1014 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = X0 ∨ (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq204 eq12
    | (have j0 := eq12 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq204 X0
       grind)
    | exact resolve eq12 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1023 : y ≠ (M.op x y) ∨ x = (M.op y y) ∨ x = (k x y) := by
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
  have eq1024 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1025 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = X0 ∨ (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq1014 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq1026 : ∀ X0 : G, (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = X0 ∨ (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have j0 := eq1012 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012
  have eq1027 : ∀ X0 : G, (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq204 eq1025
    | (have j0 := eq1025 X0
       grind)
    | exact resolve eq1025 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025
  have eq1029 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = X0 ∨ (M.op (M.op x y) y) = X0 := by
    intro X0
    first
    | exact superpose eq192 eq1026
    | (have j0 := eq1026 X0
       grind)
    | exact resolve eq1026 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq1026
  have eq1052 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq1053 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1055 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op X1 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1065 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X1)) = (M.op (k X0 X1) X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq1095 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X0 (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq180 X0
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq180
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq180 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1099 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1100 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1101 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1100 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100
  have eq1102 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X0 (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1095 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095
  have eq1115 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op X1 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq1055 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055
  have eq1144 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1101 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1101
    | (have j0 := eq1101 (σ X0)
       grind)
    | exact resolve eq1101 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1215 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1052
       grind)
    | exact superpose eq1052 eq40
    | exact resolve eq40 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1216 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1215
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1215
    | exact resolve eq1215 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215
  have eq1218 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1216
    | exact resolve eq1216 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216
  have eq1834 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1218 eq1053
    | exact resolve eq1053 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1841 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1834
       have r₂ := eq27
       grind)
    | exact resolve eq1834 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1834
  have eq1867 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1841 eq824
    | exact resolve eq824 eq1841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1841
  have eq1870 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26 eq1867
    | exact resolve eq1867 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1867
  have eq1886 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1218 eq1870
    | exact resolve eq1870 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1870
  have eq1894 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1886
       have r₂ := eq27
       grind)
    | exact resolve eq1886 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886
  have eq1918 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq824 y y
       have i₂ := eq1894
       grind)
    | exact superpose eq1894 eq824
    | exact resolve eq824 eq1894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894
  have eq1921 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1918
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1918
    | exact resolve eq1918 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1918
  have eq1953 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1921
       grind)
    | exact superpose eq1921 eq40
    | exact resolve eq40 eq1921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1921
  have eq1954 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1953
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1953
    | exact resolve eq1953 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1953
  have eq1956 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1954
    | exact resolve eq1954 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1954
  have eq2153 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1956 eq1053
    | exact resolve eq1053 eq1956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2157 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2153
  have eq2162 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2157
       have r₂ := eq27
       grind)
    | exact resolve eq2157 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2157
  have eq2201 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2162 eq824
    | exact resolve eq824 eq2162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2162
  have eq2204 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2201
    | exact resolve eq2201 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2201
  have eq2220 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1956 eq2204
    | exact resolve eq2204 eq1956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1956 eq2204
  have eq2228 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2220
       have r₂ := eq27
       grind)
    | exact resolve eq2220 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2220
  have eq2230 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2228 eq27
    | exact resolve eq27 eq2228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2233 : (M.op (σ y) (σ y)) = (k (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2228 eq835
    | exact resolve eq835 eq2228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq2234 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2228 eq1024
    | (have r₁ := eq1024
       have r₂ := eq2228
       grind)
    | exact resolve eq1024 eq2228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq2236 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2234
  have eq3149 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2236 eq152
    | exact resolve eq152 eq2236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq2236
  have eq3159 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq3149
    | exact resolve eq3149 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3149
  have eq3167 : (k (τ (σ x)) y) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3159 eq840
    | exact resolve eq840 eq3159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3205 : (k x y) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq3167
    | exact resolve eq3167 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3167
  have eq3221 : (k x y) = (τ (M.op (σ y) (σ y))) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2228 eq3205
    | exact resolve eq3205 eq2228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3205
  have eq3233 : (τ (σ x)) = (k x y) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3159 eq3221
    | exact resolve eq3221 eq3159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3159 eq3221
  have eq3242 : x = (k x y) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq3233
    | exact resolve eq3233 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3233
  have eq3243 : x = (k x y) ∨ y = (M.op x y) := by grind
  clear eq3242
  have eq3252 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1052
       have i₂ := eq3243
       grind)
    | exact superpose eq3243 eq1052
    | exact resolve eq1052 eq3243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052
  have eq3254 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq3243
       grind)
    | exact superpose eq3243 eq40
    | exact resolve eq40 eq3243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3256 : x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq3252
  have eq3262 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3254
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3254
    | exact resolve eq3254 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3254
  have eq3270 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3262 eq1218
    | exact resolve eq1218 eq3262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218
  have eq3276 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3270
  have eq3318 : ∀ X0 : G, (k x y) = (M.op X0 x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq823 y x
       have i₂ := eq3256
       grind)
    | exact superpose eq3256 eq823
    | exact resolve eq823 eq3256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3321 : ∀ X0 : G, (M.op x y) = (M.op X0 x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq3256
       grind)
    | exact superpose eq3256 eq16
    | exact resolve eq16 eq3256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3256
  have eq3334 : ∀ X0 : G, (M.op x y) = (M.op X0 x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3321 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3321
    | (have j0 := eq3321 X0
       grind)
    | exact resolve eq3321 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3321
  have eq3335 : ∀ X0 : G, x = (M.op X0 x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3243 eq3318
    | exact resolve eq3318 eq3243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3318
  have eq3350 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3334 eq3335
    | exact resolve eq3335 eq3334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3334 eq3335
  have eq3351 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq3350
  have eq3365 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3351
       grind)
    | exact superpose eq3351 eq18
    | exact resolve eq18 eq3351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3366 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq3351
       grind)
    | exact superpose eq3351 eq24
    | exact resolve eq24 eq3351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3372 : (M.op (M.op x y) (M.op x y)) = (k (M.op (M.op x y) (M.op x y)) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq825
       have i₂ := eq3351
       grind)
    | exact superpose eq3351 eq825
    | exact resolve eq825 eq3351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3376 : (τ (M.op (M.op (σ x) (σ y)) (σ y))) = (k (τ (M.op (σ y) (σ y))) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq840
       have i₂ := eq3351
       grind)
    | exact superpose eq3351 eq840
    | exact resolve eq840 eq3351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3378 : ∀ X0 : G, (k X0 (M.op (M.op x y) (M.op x y))) = X0 ∨ (M.op (M.op x y) (M.op x y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1029 X0
       have i₂ := eq3351
       grind)
    | exact superpose eq3351 eq1029
    | exact resolve eq1029 eq3351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
  have eq3385 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq3366
    | exact resolve eq3366 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3366
  have eq3426 : (k (σ x) (σ y)) = (σ (M.op (M.op x y) y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq839
       have i₂ := eq3276
       grind)
    | exact superpose eq3276 eq839
    | exact resolve eq839 eq3276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3427 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq187 y
       have i₂ := eq3276
       grind)
    | exact superpose eq3276 eq187
    | exact resolve eq187 eq3276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3276
  have eq3467 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3427
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3427
    | exact resolve eq3427 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3427
  have eq3468 : (k (σ x) (σ y)) = (σ (M.op (M.op x y) y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3426
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3426
    | exact resolve eq3426 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3426
  have eq3489 : (σ x) = (σ (M.op (M.op x y) y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3262 eq3468
    | exact resolve eq3468 eq3262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3262 eq3468
  have eq3499 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3467 eq3489
    | exact resolve eq3489 eq3467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3467 eq3489
  have eq3502 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq3499
    | exact resolve eq3499 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3499
  have eq3503 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq3502
  have eq3513 : (k (M.op x y) y) = (τ (k (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3503 eq132
    | exact resolve eq132 eq3503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq3520 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3503 eq2230
    | exact resolve eq2230 eq3503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2230
  have eq3522 : (σ x) ≠ (σ y) ∨ y = (M.op x y) := by grind
  clear eq3520
  have eq3529 : (k x y) = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq98 eq3513
    | exact resolve eq3513 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq3513
  have eq3537 : x = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3243 eq3529
    | exact resolve eq3529 eq3243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3529
  have eq3538 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3351 eq3537
    | exact resolve eq3537 eq3351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3537
  have eq3820 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3365 eq1115
    | (have j0 := eq1115 (M.op x y) x x
       grind)
    | exact resolve eq1115 eq3365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3365
  have eq5304 : (k (σ y) (σ y)) = (k (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq2233
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq2233
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq2233 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2233
  have eq5311 : (k (σ y) (σ y)) = (k (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5304
  have eq5364 : (τ (M.op (M.op (σ x) (σ y)) (σ y))) = (k (τ (k (σ y) (σ y))) (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3376
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq3376
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq3376 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3376
  have eq5370 : (τ (M.op (M.op (σ x) (σ y)) (σ y))) = (k (τ (k (σ y) (σ y))) (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5364
  have eq5373 : (τ (M.op (M.op (σ x) (σ y)) (σ y))) = (k (k y y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq115 eq5370
    | exact resolve eq5370 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5370
  have eq5376 : (τ (M.op (M.op (σ x) (σ y)) (σ y))) = (k (k (M.op x y) (M.op x y)) (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3351 eq5373
    | exact resolve eq5373 eq3351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5373
  have eq6216 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3378 eq37
    | (have j1 := eq3378 (M.op x y)
       grind)
    | exact resolve eq37 eq3378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq3378
  have eq6224 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq6216
    | exact resolve eq6216 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6216
  have eq6231 : (σ y) = (k (σ y) (σ (M.op (M.op x y) (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3385 eq6224
    | exact resolve eq6224 eq3385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6224
  have eq6899 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op y y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1065 x y X0
       have i₂ := eq3243
       grind)
    | exact superpose eq3243 eq1065
    | (have j0 := eq1065 x y x
       grind)
    | exact resolve eq1065 eq3243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3243
  have eq7182 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6899 x
       have i₂ := eq179 x
       grind)
    | exact superpose eq179 eq6899
    | exact resolve eq6899 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq6899
  have eq7230 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7182
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7182
    | exact resolve eq7182 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7182
  have eq7245 : y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7230
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7230
    | exact resolve eq7230 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7230
  have eq7246 : y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op y y) := by grind
  clear eq7245
  have eq7252 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq3351 eq7246
    | exact resolve eq7246 eq3351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7246
  have eq12060 : (σ y) = (k (σ y) (σ (k (M.op x y) (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq6231
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq6231
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq6231 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6231
  have eq12066 : (σ y) = (k (σ y) (σ (k (M.op x y) (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq12060
  have eq12071 : (σ y) = (k (σ y) (σ (k (M.op x y) (M.op x y)))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq1101 (M.op x y)
       grind)
    | (have r₁ := eq12066
       have r₂ := eq1101 (M.op x y)
       grind)
    | exact resolve eq12066 eq1101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12066
  have eq12076 : (σ y) = (k (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq41 eq12071
    | exact resolve eq12071 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12071
  have eq12078 : (σ y) = (k (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq12076
    | exact resolve eq12076 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12076
  have eq12079 : (σ y) = (k (σ y) (k (σ y) (σ y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3385 eq12078
    | exact resolve eq12078 eq3385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12078
  have eq12084 : (τ (σ y)) = (k y (τ (k (σ y) (σ y)))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq12079 eq107
    | exact resolve eq107 eq12079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq12079
  have eq12088 : (τ (σ y)) = (k y (k y y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq115 eq12084
    | exact resolve eq12084 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12084
  have eq12090 : y = (k y (k y y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq31 eq12088
    | exact resolve eq12088 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12088
  have eq12091 : (M.op x y) = (k (M.op x y) (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3351 eq12090
    | exact resolve eq12090 eq3351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3351 eq12090
  have eq12102 : ∀ X0 : G, (M.op X0 (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq12091 eq1065
    | (have j0 := eq1065 (M.op x y) (k (M.op x y) (M.op x y)) x
       grind)
    | exact resolve eq1065 eq12091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065
  have eq12106 : ∀ X0 : G, (k (M.op x y) (k (M.op x y) (M.op x y))) = (M.op X0 (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) ∨ (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq11 eq12102
    | (have j1 := eq11 (M.op x y) (k (M.op x y) (M.op x y))
       grind)
    | exact resolve eq12102 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12102
  have eq12108 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (M.op x y))) = (k (M.op x y) (k (M.op x y) (M.op x y))) ∨ (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq3820 eq12106
    | exact resolve eq12106 eq3820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12106
  have eq12110 : (k (M.op (M.op x y) (M.op x y)) (M.op x y)) = (k (M.op x y) (k (M.op x y) (M.op x y))) ∨ (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq12108 x
       have i₂ := eq823 sF0 x
       grind)
    | exact superpose eq823 eq12108
    | exact resolve eq12108 eq823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12108
  have eq12112 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (k (M.op x y) (M.op x y))) ∨ (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3372 eq12110
    | exact resolve eq12110 eq3372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12110
  have eq12113 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (k (M.op x y) (M.op x y))) ∨ (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (M.op x y) (k (M.op x y) (M.op x y))
       grind)
    | (have r₁ := eq12112
       have r₂ := eq13 (k (M.op x y) (k (M.op x y) (M.op x y))) (M.op x y)
       grind)
    | (have r₁ := eq12112
       have r₂ := eq13 (M.op x y) (k (M.op x y) (M.op x y))
       grind)
    | (have r₁ := eq12112
       have r₂ := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq12112 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12112
  have eq12114 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq12091 eq12113
    | exact resolve eq12113 eq12091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12091 eq12113
  have eq12115 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq12114
  have eq15015 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12115 eq3820
    | exact resolve eq3820 eq12115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3820 eq12115
  have eq15029 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq15015
  have eq15045 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq15029
       have r₂ := eq13 (k (M.op x y) (M.op x y)) (M.op x y)
       grind)
    | (have r₁ := eq15029
       have r₂ := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq15029 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15029
  have eq15066 : (k (M.op x y) (M.op x y)) = (k (k (M.op x y) (M.op x y)) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15045 eq3372
    | exact resolve eq3372 eq15045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3372
  have eq15102 : ∀ X0 : G, (k (k (M.op x y) (M.op x y)) (M.op x y)) = (M.op (M.op X0 (k (M.op x y) (M.op x y))) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15045 eq821
    | exact resolve eq821 eq15045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15103 : ∀ X0 : G, (M.op X0 (k (M.op x y) (M.op x y))) = (k (k (M.op x y) (M.op x y)) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15045 eq823
    | exact resolve eq823 eq15045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15045
  have eq15139 : (k (M.op x y) (M.op x y)) = (k (k (M.op x y) (M.op x y)) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq15066
  have eq15151 : (k (k (M.op x y) (M.op x y)) (M.op x y)) = (M.op (k (k (M.op x y) (M.op x y)) (M.op x y)) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15103 eq15102
    | exact resolve eq15102 eq15103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15102 eq15103
  have eq15175 : (k (M.op x y) (M.op x y)) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15139 eq15151
    | exact resolve eq15151 eq15139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15151
  have eq18436 : (k (M.op x y) (M.op x y)) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq5376 eq15139
    | exact resolve eq15139 eq5376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5376 eq15139
  have eq18451 : (k (M.op x y) (M.op x y)) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq18436
  have eq18471 : (σ (k (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq18451 eq14
    | exact resolve eq14 eq18451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18480 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq41 eq18471
    | exact resolve eq18471 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq18471
  have eq18484 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq18480
    | exact resolve eq18480 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18480
  have eq18486 : (k (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3385 eq18484
    | exact resolve eq18484 eq3385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18484
  have eq21213 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq5311 eq1099
    | (have j0 := eq1099 (k (σ y) (σ y)) (k (σ y) (σ y))
       grind)
    | (have r₁ := eq1099 (k (σ y) (σ y)) (k (σ y) (σ y))
       have r₂ := eq5311
       grind)
    | exact resolve eq1099 eq5311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099 eq5311
  have eq21214 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq21213
  have eq21215 : (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq21214
  have eq21411 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq21215 eq1115
    | (have j0 := eq1115 (σ y) x x
       grind)
    | exact resolve eq1115 eq21215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21215
  have eq21449 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21411 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21411
  have eq21476 : (k (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq199 eq21449
    | (have j0 := eq21449 (σ x)
       grind)
    | exact resolve eq21449 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21449
  have eq21493 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2228 eq21476
    | exact resolve eq21476 eq2228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21476
  have eq21507 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq21493
       have r₂ := eq13 (k (σ y) (σ y)) (σ y)
       grind)
    | (have r₁ := eq21493
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq21493 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21493
  have eq21528 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X0 (k (σ y) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21507 eq180
    | exact resolve eq180 eq21507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq21552 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (k (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21507 eq199
    | exact resolve eq199 eq21507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq21562 : ∀ X0 X1 : G, (M.op X0 (k (σ y) (σ y))) = (M.op X1 (k (k (σ y) (σ y)) (σ y))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq21507 eq705
    | exact resolve eq705 eq21507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq21565 : ∀ X0 : G, (k (k (σ y) (σ y)) (σ y)) = (M.op X0 (k (σ y) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21507 eq823
    | exact resolve eq823 eq21507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21628 : ∀ X1 : G, (k (k (σ y) (σ y)) (σ y)) = (M.op X1 (k (k (σ y) (σ y)) (σ y))) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq21565 eq21562
    | exact resolve eq21562 eq21565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21562
  have eq21636 : (M.op (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2228 eq21552
    | exact resolve eq21552 eq2228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21552
  have eq21646 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (k (σ y) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2228 eq21528
    | exact resolve eq21528 eq2228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21528
  have eq21663 : (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21507 eq21636
    | exact resolve eq21636 eq21507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21636
  have eq21667 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op X0 (k (σ y) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21507 eq21646
    | exact resolve eq21646 eq21507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21507 eq21646
  have eq21854 : ∀ X0 : G, (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) = X0 ∨ (k X0 (k (σ y) (σ y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21667 eq12
    | (have j0 := eq12 X0 (k (σ y) (σ y))
       grind)
    | (have r₁ := eq12 X0 (k (σ y) (σ y))
       have r₂ := eq21667 X0
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq21667 X0
       grind)
    | exact resolve eq12 eq21667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21667
  have eq21895 : ∀ X0 : G, (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) = X0 ∨ (k X0 (k (σ y) (σ y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21854 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21854
  have eq25294 : ∀ X0 : G, (k (k (σ y) (σ y)) (σ y)) = X0 ∨ y = (M.op x y) ∨ (k X0 (k (σ y) (σ y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq21565 X0
       have i₂ := eq21895 (M.op X0 (k sF3 sF3))
       grind)
    | exact superpose eq21895 eq21565
    | (have j1 := eq21895 X0
       grind)
    | exact resolve eq21565 eq21895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21565
  have eq25312 : ∀ X0 X1 : G, (k X0 (k (σ y) (σ y))) = (M.op X1 X0) ∨ (k X0 (k (σ y) (σ y))) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq823 X0 X1
       have i₂ := eq21895 (M.op X0 X0)
       grind)
    | exact superpose eq21895 eq823
    | (have j1 := eq21895 X0
       grind)
    | exact resolve eq823 eq21895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21895
  have eq25345 : ∀ X0 : G, (k (k (σ y) (σ y)) (σ y)) = X0 ∨ y = (M.op x y) ∨ (k X0 (k (σ y) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq25294 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25294
  have eq25493 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (k X0 (k (σ y) (σ y))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21628 X1
       have i₂ := eq25345 (k (k sF3 sF3) sF3)
       grind)
    | exact superpose eq25345 eq21628
    | (have j1 := eq25345 X0
       grind)
    | exact resolve eq21628 eq25345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21628 eq25345
  have eq25499 : ∀ X0 X1 : G, (k X0 (k (σ y) (σ y))) = X0 ∨ y = (M.op x y) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq25493 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25493
  have eq28788 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 (k (σ y) (σ y))) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq25312 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25312
  have eq28964 : ∀ X0 : G, (k X0 (k (σ y) (σ y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq28788 X0 x
       have j1 := eq25499 X0 x
       grind)
    | (have r₁ := eq28788 y x
       have r₂ := eq25499 X0 x
       grind)
    | (have r₁ := eq28788 X0 x
       have r₂ := eq25499 X0 x
       grind)
    | exact resolve eq28788 eq25499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25499 eq28788
  have eq29122 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (k (σ y) (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28964 eq419
    | exact resolve eq419 eq28964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28964
  have eq29152 : ∀ X0 : G, (τ (σ X0)) = (k X0 (k y y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq115 eq29122
    | exact resolve eq29122 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq29122
  have eq29163 : ∀ X0 : G, (k X0 (k y y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq29152 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq29152
    | exact resolve eq29152 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29152
  have eq29197 : (k y y) ≠ (k y y) ∨ (k y y) = (M.op (k y y) (k y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1101 (k y y)
       have i₂ := eq29163 (k y y)
       grind)
    | exact superpose eq29163 eq1101
    | (have j0 := eq1101 (k y y)
       grind)
    | (have r₁ := eq1101 (k y y)
       have r₂ := eq29163 (k y y)
       grind)
    | exact resolve eq1101 eq29163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101 eq29163
  have eq29218 : (k y y) = (M.op (k y y) (k y y)) ∨ y = (M.op x y) := by grind
  clear eq29197
  have eq30117 : ∀ X0 : G, (k y y) = (M.op (M.op X0 y) y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1115 y (k y y) X0
       have i₂ := eq29218
       grind)
    | exact superpose eq29218 eq1115
    | (have j0 := eq1115 y x x
       grind)
    | exact resolve eq1115 eq29218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115 eq29218
  have eq30186 : (k y y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq30117 x
       have i₂ := eq187 x
       grind)
    | (have i₁ := eq30117 x
       have i₂ := eq187 x
       grind)
    | exact superpose eq187 eq30117
    | (have j0 := eq30117 x
       grind)
    | exact resolve eq30117 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq30117
  have eq31545 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30186 eq7252
    | exact resolve eq7252 eq30186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30186
  have eq31572 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by grind
  clear eq31545
  have eq35080 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq31572
       grind)
    | exact superpose eq31572 eq40
    | exact resolve eq40 eq31572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31572
  have eq35167 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq35080
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35080
    | exact resolve eq35080 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35080
  have eq35176 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq35167
    | exact resolve eq35167 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35167
  have eq35179 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3503 eq35176
    | exact resolve eq35176 eq3503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35176
  have eq35519 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq35179 eq21663
    | exact resolve eq21663 eq35179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35179
  have eq35651 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by grind
  clear eq35519
  have eq35683 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq35651
    | exact resolve eq35651 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35651
  have eq35701 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2228 eq35683
    | exact resolve eq35683 eq2228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35683
  have eq35718 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq35701
       have r₂ := eq3522
       grind)
    | exact resolve eq35701 eq3522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35701
  have eq35763 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq35718
       grind)
    | exact superpose eq35718 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq35718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35773 : (k (M.op x y) y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq824 y y
       have i₂ := eq35718
       grind)
    | exact superpose eq35718 eq824
    | exact resolve eq824 eq35718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35718
  have eq35785 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq35763
  have eq35801 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3538 eq35773
    | exact resolve eq35773 eq3538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3538 eq35773
  have eq35835 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7252 eq35801
    | exact resolve eq35801 eq7252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7252 eq35801
  have eq35836 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by grind
  clear eq35835
  have eq36088 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq35785
       grind)
    | exact superpose eq35785 eq40
    | exact resolve eq40 eq35785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35785
  have eq36175 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq36088
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36088
    | exact resolve eq36088 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36088
  have eq36183 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq36175
    | exact resolve eq36175 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36175
  have eq36186 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3503 eq36183
    | exact resolve eq36183 eq3503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36183
  have eq36352 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq36186 eq21663
    | exact resolve eq21663 eq36186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21663 eq36186
  have eq36484 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq36352
  have eq36516 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq36484
    | exact resolve eq36484 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36484
  have eq36534 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2228 eq36516
    | exact resolve eq36516 eq2228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2228 eq36516
  have eq36551 : y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq36534
       have r₂ := eq3522
       grind)
    | exact resolve eq36534 eq3522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36534
  have eq36572 : (k (σ y) (σ y)) = (σ (M.op (M.op x y) y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq839
       have i₂ := eq36551
       grind)
    | exact superpose eq36551 eq839
    | exact resolve eq839 eq36551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36614 : (k y y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq824 y y
       have i₂ := eq36551
       grind)
    | exact superpose eq36551 eq824
    | exact resolve eq824 eq36551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36645 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36551 eq36614
    | exact resolve eq36614 eq36551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36551 eq36614
  have eq36664 : (k (σ y) (σ y)) = (σ (M.op (M.op x y) y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq36572
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36572
    | exact resolve eq36572 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36572
  have eq36675 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35836 eq36664
    | exact resolve eq36664 eq35836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35836 eq36664
  have eq36678 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq36675
    | exact resolve eq36675 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36675
  have eq36680 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3503 eq36678
    | exact resolve eq36678 eq3503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3503 eq36678
  have eq36763 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq36645
       grind)
    | exact superpose eq36645 eq40
    | exact resolve eq40 eq36645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36645
  have eq36854 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq36763
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36763
    | exact resolve eq36763 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36763
  have eq36860 : (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36680 eq36854
    | exact resolve eq36854 eq36680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36680 eq36854
  have eq36863 : y = (M.op x y) := by
    first
    | (have r₁ := eq36860
       have r₂ := eq3522
       grind)
    | exact resolve eq36860 eq3522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3522 eq36860
  have eq37579 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq36863
       grind)
    | exact superpose eq36863 eq18
    | exact resolve eq18 eq36863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq37580 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq36863
       grind)
    | exact superpose eq36863 eq24
    | exact resolve eq24 eq36863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq37582 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq36863
       grind)
    | exact superpose eq36863 eq40
    | exact resolve eq40 eq36863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq37587 : (M.op (M.op x y) (M.op x y)) = (k (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq825
       have i₂ := eq36863
       grind)
    | exact superpose eq36863 eq825
    | exact resolve eq825 eq36863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq37589 : (M.op (M.op x y) (M.op x y)) = (k (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq837
       have i₂ := eq36863
       grind)
    | exact superpose eq36863 eq837
    | exact resolve eq837 eq36863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq37590 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq839
       have i₂ := eq36863
       grind)
    | exact superpose eq36863 eq839
    | exact resolve eq839 eq36863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq37591 : (τ (M.op (M.op (σ x) (σ y)) (σ y))) = (k (τ (M.op (σ y) (σ y))) (M.op x y)) := by
    first
    | (have i₁ := eq840
       have i₂ := eq36863
       grind)
    | exact superpose eq36863 eq840
    | exact resolve eq840 eq36863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq37592 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq1023
       have i₂ := eq36863
       grind)
    | exact superpose eq36863 eq1023
    | (have r₁ := eq1023
       have r₂ := eq36863
       grind)
    | exact resolve eq1023 eq36863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023
  have eq37595 : x = (k x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq37592
  have eq37601 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq37580 eq20
    | exact resolve eq20 eq37580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37636 : ∀ X0 : G, (τ (k (σ y) X0)) = (k (M.op x y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq37580 eq419
    | exact resolve eq419 eq37580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq39338 : (τ (σ y)) = (k (M.op x y) (τ (M.op (M.op (σ x) (σ y)) (σ y)))) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq1027 eq37636
    | (have j1 := eq1027 (σ y)
       grind)
    | exact resolve eq37636 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027 eq37636
  have eq39474 : y = (k (M.op x y) (τ (M.op (M.op (σ x) (σ y)) (σ y)))) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq31 eq39338
    | exact resolve eq39338 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39338
  have eq39506 : (M.op x y) = (k (M.op x y) (τ (M.op (M.op (σ x) (σ y)) (σ y)))) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq39474
       have i₂ := eq36863
       grind)
    | exact superpose eq36863 eq39474
    | exact resolve eq39474 eq36863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39474
  have eq39905 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq37595 eq37582
    | exact resolve eq37582 eq37595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37595
  have eq39910 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq39905
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq39905
    | exact resolve eq39905 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39905
  have eq39921 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq39910 eq1053
    | exact resolve eq1053 eq39910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053
  have eq53751 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq39921 eq824
    | exact resolve eq824 eq39921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39921
  have eq53767 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26 eq53751
    | exact resolve eq53751 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53751
  have eq53803 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq39910 eq53767
    | exact resolve eq53767 eq39910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39910 eq53767
  have eq53804 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq53803
  have eq53854 : x = (k x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53804 eq37587
    | exact resolve eq37587 eq53804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37587
  have eq53855 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53804 eq37589
    | exact resolve eq37589 eq53804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37589
  have eq53856 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53804 eq37590
    | exact resolve eq37590 eq53804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37590
  have eq53895 : ∀ X0 : G, (k x (M.op x y)) = (M.op (M.op X0 x) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq53804 eq821
    | exact resolve eq821 eq53804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53896 : ∀ X0 : G, (k x (M.op x y)) = (M.op X0 x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq53804 eq823
    | exact resolve eq823 eq53804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq53907 : ∀ X0 : G, (M.op X0 x) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq53804 eq16
    | exact resolve eq16 eq53804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53916 : (k x (M.op x y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53804 eq824
    | exact resolve eq824 eq53804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53804
  have eq53935 : (M.op x y) = (k x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37579 eq53916
    | exact resolve eq53916 eq37579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53916
  have eq53944 : ∀ X0 : G, (M.op x y) = (M.op X0 x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq37579 eq53907
    | exact resolve eq53907 eq37579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53907
  have eq53949 : (k x (M.op x y)) = (M.op (k x (M.op x y)) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53896 eq53895
    | exact resolve eq53895 eq53896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53895 eq53896
  have eq53966 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53856
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq53856
    | exact resolve eq53856 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53856
  have eq53988 : x = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53854 eq53949
    | exact resolve eq53949 eq53854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53854 eq53949
  have eq54011 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37579 eq53988
    | exact resolve eq53988 eq37579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53988
  have eq54046 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54011 eq27
    | exact resolve eq27 eq54011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54011
  have eq54064 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq54046
       have r₂ := eq3385
       grind)
    | exact resolve eq54046 eq3385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3385 eq54046
  have eq54068 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq54064 eq27
    | exact resolve eq27 eq54064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54083 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq54064 eq18451
    | exact resolve eq18451 eq54064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18451
  have eq54084 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq54064 eq18486
    | exact resolve eq18486 eq54064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18486
  have eq54087 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq54084
  have eq54088 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq54083
  have eq54092 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq54087
    | exact resolve eq54087 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54087
  have eq54093 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq54088
    | exact resolve eq54088 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54088
  have eq54099 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37601 eq54068
    | exact resolve eq54068 eq37601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54068
  have eq54102 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq54064 eq54092
    | exact resolve eq54092 eq54064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54092
  have eq54103 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq54064 eq54093
    | exact resolve eq54093 eq54064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54093
  have eq54111 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq29 eq54103
    | exact resolve eq54103 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54103
  have eq58012 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53935 eq35
    | exact resolve eq35 eq53935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq53935
  have eq58041 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq58012
    | exact resolve eq58012 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58012
  have eq58046 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37601 eq58041
    | exact resolve eq58041 eq37601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58041
  have eq58051 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53966 eq58046
    | exact resolve eq58046 eq53966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53966 eq58046
  have eq58057 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq58051 eq27
    | exact resolve eq27 eq58051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58051
  have eq58075 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq58057
       have r₂ := eq37601
       grind)
    | exact resolve eq58057 eq37601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58057
  have eq58081 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq58075 eq204
    | exact resolve eq204 eq58075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq58097 : (M.op x y) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq58075 eq39506
    | exact resolve eq39506 eq58075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39506
  have eq58109 : (M.op x y) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq58097
    | exact resolve eq58097 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58097
  have eq58116 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq26 eq58081
    | (have j0 := eq58081 X0
       grind)
    | exact resolve eq58081 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58081
  have eq58119 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq58109
    | exact resolve eq58109 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58109
  have eq58126 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq58075 eq58116
    | exact resolve eq58116 eq58075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58116
  have eq58128 : (σ x) = (σ y) ∨ (M.op x y) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq58075 eq58119
    | exact resolve eq58119 eq58075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58119
  have eq58129 : (σ x) = (σ y) ∨ (M.op x y) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) := by grind
  clear eq58128
  have eq58134 : (σ x) = (σ y) ∨ (M.op x y) = (k (M.op x y) (τ (σ x))) := by
    first
    | exact superpose eq58075 eq58129
    | exact resolve eq58129 eq58075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58129
  have eq58138 : (M.op x y) = (k (M.op x y) x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29 eq58134
    | exact resolve eq58134 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58134
  have eq59772 : ∀ X0 : G, (k (M.op x y) x) = (M.op (M.op X0 (M.op x y)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq821 x x
       have i₂ := eq53944 x
       grind)
    | exact superpose eq53944 eq821
    | exact resolve eq821 eq53944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq59882 : (M.op x y) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53944 eq59772
    | exact resolve eq59772 eq53944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53944 eq59772
  have eq59952 : (M.op x y) = (k (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq58138 eq59882
    | exact resolve eq59882 eq58138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58138 eq59882
  have eq59953 : (M.op x y) = (k (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq59952
  have eq60014 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54064 eq59953
    | exact resolve eq59953 eq54064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59953
  have eq60171 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq60014 eq37582
    | exact resolve eq37582 eq60014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37582 eq60014
  have eq60182 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq60171
    | exact resolve eq60171 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60171
  have eq60191 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37601 eq60182
    | exact resolve eq60182 eq37601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37601 eq60182
  have eq60200 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq58075 eq60191
    | exact resolve eq60191 eq58075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58075 eq60191
  have eq61267 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1144 x
       have i₂ := eq53855
       grind)
    | exact superpose eq53855 eq1144
    | (have j0 := eq1144 x
       grind)
    | exact resolve eq1144 eq53855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144 eq53855
  have eq61341 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq61267
  have eq61455 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq61341
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq61341
    | exact resolve eq61341 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61341
  have eq61493 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq58126 eq61455
    | (have j1 := eq58126 (σ x)
       grind)
    | exact resolve eq61455 eq58126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58126 eq61455
  have eq61494 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq61493
  have eq61621 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq61494 eq16
    | exact resolve eq16 eq61494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61650 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq61494 eq61621
    | exact resolve eq61621 eq61494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61621
  have eq75501 : (k (τ (σ y)) (M.op x y)) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq54102 eq37591
    | exact resolve eq37591 eq54102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37591 eq54102
  have eq75588 : (k y (M.op x y)) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq31 eq75501
    | exact resolve eq75501 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq75501
  have eq75612 : (k (M.op x y) (M.op x y)) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq75588
       have i₂ := eq36863
       grind)
    | exact superpose eq36863 eq75588
    | exact resolve eq75588 eq36863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36863 eq75588
  have eq75629 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq54064 eq75612
    | exact resolve eq75612 eq54064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75612
  have eq75643 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq75629
    | exact resolve eq75629 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75629
  have eq75649 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq54064 eq75643
    | exact resolve eq75643 eq54064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54064 eq75643
  have eq75653 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq29 eq75649
    | exact resolve eq75649 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq75649
  have eq75733 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq54111 eq824
    | exact resolve eq824 eq54111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq75753 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq54111 eq75733
    | exact resolve eq75733 eq54111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54111 eq75733
  have eq75786 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq75653 eq75753
    | exact resolve eq75753 eq75653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75653 eq75753
  have eq75801 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq75786
       have r₂ := eq54099
       grind)
    | exact resolve eq75786 eq54099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54099 eq75786
  have eq75851 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq75801 eq15175
    | exact resolve eq15175 eq75801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15175 eq75801
  have eq75919 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq75851
  have eq75976 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37579 eq75919
    | exact resolve eq75919 eq37579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37579 eq75919
  have eq75977 : x = (M.op x y) := by grind
  clear eq75976
  have eq75998 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq75977
       grind)
    | exact superpose eq75977 eq22
    | exact resolve eq22 eq75977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq75977
  have eq79200 : (σ x) = (σ y) := by
    first
    | exact superpose eq75998 eq37580
    | exact resolve eq37580 eq75998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37580
  have eq79201 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq75998 eq20
    | exact resolve eq20 eq75998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq75998
  have eq79336 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq79200 eq26
    | exact resolve eq26 eq79200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq79362 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op X0 (k (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq79200 eq1102
    | exact resolve eq1102 eq79200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102 eq79200
  have eq79582 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (k (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq61494 eq79362
    | exact resolve eq79362 eq61494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61494 eq79362
  have eq79604 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (k (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq79336 eq79582
    | exact resolve eq79582 eq79336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79582
  have eq79617 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op X0 (k (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq79336 eq79604
    | (have j0 := eq79604 X0
       grind)
    | exact resolve eq79604 eq79336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79336 eq79604
  have eq79622 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq60200 eq79617
    | exact resolve eq79617 eq60200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60200 eq79617
  have eq79626 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq61650 eq79622
    | exact resolve eq79622 eq61650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61650 eq79622
  have eq79627 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq79626
  have eq79677 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq79627 eq27
    | exact resolve eq27 eq79627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq79627
  have eq79705 : False := by grind
  exact eq79705

/-- `Equation4494`: `x ◇ (y ◇ y) = (z ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pyy_x_pxy_Equation4494 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4494 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4494.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = a :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
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
  clear eq35
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
  clear eq39
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
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
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
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
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq175 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X3 X1) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 x X1 X3
       have i₂ := eq16 x X1 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op X0 (M.op y y)) = (M.op (M.op x y) y) := by
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
  have eq180 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq16 X2 X1 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1) x
       have i₂ := eq16 (M.op x (M.op X1 X1)) X1 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (M.op X1 y) y) := by
    intro X1
    first
    | (have i₁ := eq16 x y X1
       have i₂ := eq179 x
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, (M.op (M.op x y) y) ≠ X0 ∨ (M.op (M.op x y) y) = (k X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op y y)
       have i₂ := eq179 (M.op y y)
       grind)
    | exact superpose eq179 eq13
    | (have r₁ := eq13 (M.op (M.op x y) y) (M.op y y)
       have r₂ := eq179 (M.op y y)
       grind)
    | exact resolve eq13 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op y y) (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op y y) x
       have i₂ := eq179 (M.op x (M.op y y))
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq191 X0
       have i₂ := eq179 (M.op y y)
       grind)
    | exact superpose eq179 eq191
    | exact resolve eq191 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq203 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X0 (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) := by
    intro X0
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq180 eq203
    | exact resolve eq203 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq213 : (σ (M.op y y)) = (k (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq40 (M.op y y)
       have i₂ := eq184 y
       grind)
    | exact superpose eq184 eq40
    | exact resolve eq40 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq192 eq184
    | exact resolve eq184 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277 : (τ (M.op (σ x) (σ x))) = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | (have i₁ := eq141 (M.op sF2 sF2)
       have i₂ := eq184 sF2
       grind)
    | exact superpose eq184 eq141
    | exact resolve eq141 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq298 : (τ (M.op (σ y) (σ y))) = (k (τ (M.op (σ y) (σ y))) y) := by
    first
    | (have i₁ := eq152 (M.op sF3 sF3)
       have i₂ := eq184 sF3
       grind)
    | exact superpose eq184 eq152
    | exact resolve eq152 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq756 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = X0 ∨ (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq204 eq12
    | (have j0 := eq12 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq204 X0
       grind)
    | exact resolve eq12 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq762 : y ≠ (M.op x y) ∨ x = (M.op y y) ∨ x = (k x y) := by
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
  have eq763 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq764 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = X0 ∨ (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq756 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq766 : ∀ X0 : G, (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq204 eq764
    | (have j0 := eq764 X0
       grind)
    | exact resolve eq764 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq773 : ∀ X0 : G, (M.op (M.op x y) y) = (k X0 (M.op y y)) ∨ (M.op y y) = (M.op (M.op x y) y) ∨ (M.op (M.op y y) (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 X0 (M.op y y)
       have i₂ := eq179 X0
       grind)
    | exact superpose eq179 eq11
    | (have j0 := eq11 (M.op (M.op x y) y) y
       grind)
    | exact resolve eq11 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq780 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq781 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq785 : ∀ X0 X1 X2 : G, (M.op X1 (k X0 X0)) = (M.op (M.op X2 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq789 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X1)) = (M.op (k X0 X1) X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq816 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X0 (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq180 X0
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq180
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq180 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq820 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq821 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq822 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq821 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq823 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X0 (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq816 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq832 : ∀ X0 X1 X2 : G, (M.op X1 (k X0 X0)) = (M.op (M.op X2 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq785 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq847 : ∀ X0 : G, (M.op (M.op x y) y) = X0 ∨ (M.op (M.op x y) y) = (k X0 (M.op y y)) ∨ (M.op y y) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq773 X0
       have i₂ := eq179 (M.op y y)
       grind)
    | exact superpose eq179 eq773
    | (have j0 := eq773 X0
       grind)
    | exact resolve eq773 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq854 : ∀ X0 : G, (M.op (M.op x y) y) = (k X0 (M.op y y)) ∨ (M.op y y) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have j0 := eq847 (k X0 (M.op y y))
       have j1 := eq188 X0
       grind)
    | (have r₁ := eq847 X0
       have r₂ := eq188 X0
       grind)
    | (have r₁ := eq847 (M.op (M.op x y) y)
       have r₂ := eq188 (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq847 X0
       have r₂ := eq188 (k X0 (M.op y y))
       grind)
    | exact resolve eq847 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq847
  have eq857 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq822 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq822
    | (have j0 := eq822 (σ X0)
       grind)
    | exact resolve eq822 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1005 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq780
       grind)
    | exact superpose eq780 eq40
    | exact resolve eq40 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1006 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1005
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1005
    | exact resolve eq1005 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005
  have eq1008 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1006
    | exact resolve eq1006 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006
  have eq1126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1008 eq781
    | exact resolve eq781 eq1008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1133 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1126
       have r₂ := eq27
       grind)
    | exact resolve eq1126 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126
  have eq1138 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1133 eq298
    | exact resolve eq298 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1149 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1133 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133
  have eq1154 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq1149
  have eq1163 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq1138
    | exact resolve eq1138 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138
  have eq1168 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1163
       have r₂ := eq762
       grind)
    | exact resolve eq1163 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762 eq1163
  have eq1170 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq780
       have i₂ := eq1168
       grind)
    | exact superpose eq1168 eq780
    | exact resolve eq780 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1172 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1168
       grind)
    | exact superpose eq1168 eq40
    | exact resolve eq40 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1173 : x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1170
  have eq1175 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1172
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1172
    | exact resolve eq1172 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq1181 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1175 eq781
    | exact resolve eq781 eq1175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175
  have eq1185 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq1181
  have eq1193 : x = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1173
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq1173
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq1173 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1194 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq213
       have i₂ := eq1173
       grind)
    | exact superpose eq1173 eq213
    | exact resolve eq213 eq1173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1196 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq179 X0
       have i₂ := eq1173
       grind)
    | exact superpose eq1173 eq179
    | exact resolve eq179 eq1173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1197 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq187 y
       have i₂ := eq1173
       grind)
    | exact superpose eq1173 eq187
    | exact resolve eq187 eq1173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1205 : x = (k y y) ∨ x = y ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq1173
       grind)
    | exact superpose eq1173 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq1173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1209 : ∀ X0 : G, (M.op x y) = (M.op X0 x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq1173
       grind)
    | exact superpose eq1173 eq16
    | exact resolve eq16 eq1173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173
  have eq1210 : x = (k y y) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1205
  have eq1211 : x = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq1193
  have eq1212 : ∀ X0 : G, (M.op x y) = (M.op X0 x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1209 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1209
    | (have j0 := eq1209 X0
       grind)
    | exact resolve eq1209 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq1218 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1197
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1197
    | exact resolve eq1197 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197
  have eq1219 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1194
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1194
    | exact resolve eq1194 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194
  have eq1220 : x = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1210 eq1211
    | exact resolve eq1211 eq1210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210 eq1211
  have eq1224 : x = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1212 eq1220
    | exact resolve eq1220 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220
  have eq1225 : x = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1224
  have eq1282 : ∀ X0 : G, (M.op x y) = (k X0 x) ∨ x = (M.op x y) ∨ (M.op x x) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11 X0 x
       have i₂ := eq1212 X0
       grind)
    | exact superpose eq1212 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq1294 : ∀ X0 : G, (M.op x y) = (k X0 x) ∨ x = (M.op x y) ∨ (M.op x x) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1282 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282
  have eq1324 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1219 eq781
    | exact resolve eq781 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219
  have eq1328 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1324
  have eq1337 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1225
       grind)
    | exact superpose eq1225 eq40
    | exact resolve eq40 eq1225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1340 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1337
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1337
    | exact resolve eq1337 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337
  have eq1342 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1340
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1340
    | exact resolve eq1340 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340
  have eq1501 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X1) = (M.op X3 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq182 X2 X1 X3
       have i₂ := eq181 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq182 X2 X1 X3
       have i₂ := eq181 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq181 eq182
    | exact resolve eq182 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1502 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X1) = (M.op X3 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq182 X2 X1 X3
       have i₂ := eq16 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq16 eq182
    | exact resolve eq182 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2131 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1185 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq1185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2133 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1185 eq16
    | exact resolve eq16 eq1185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185
  have eq2138 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq2131
  have eq2144 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq26 eq2133
    | (have j0 := eq2133 X0
       grind)
    | exact resolve eq2133 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2133
  have eq2892 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) X1) = (M.op X2 (k X1 X1)) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq832 X1 X2 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq832
    | (have j0 := eq832 X1 X1 X2
       have j1 := eq11 X1 X1
       grind)
    | exact resolve eq832 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4391 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1328 eq16
    | exact resolve eq16 eq1328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328
  have eq4406 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq4391
    | (have j0 := eq4391 X0
       grind)
    | exact resolve eq4391 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4391
  have eq6552 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op y y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq789 x y X0
       have i₂ := eq1168
       grind)
    | exact superpose eq1168 eq789
    | (have j0 := eq789 x y x
       grind)
    | exact resolve eq789 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168
  have eq6580 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1342 eq789
    | (have j0 := eq789 (σ y) (σ y) x
       grind)
    | exact resolve eq789 eq1342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6762 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq6580 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6580
  have eq6773 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op y y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq6552 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6552
  have eq6820 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq180 eq6762
    | exact resolve eq6762 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6762
  have eq6833 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6773 x
       have i₂ := eq179 x
       grind)
    | exact superpose eq179 eq6773
    | exact resolve eq6773 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6773
  have eq6884 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq6820
    | exact resolve eq6820 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6820
  have eq6897 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6833
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6833
    | exact resolve eq6833 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6833
  have eq6922 : y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6897
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6897
    | exact resolve eq6897 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6897
  have eq6934 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1218 eq6922
    | exact resolve eq6922 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6922
  have eq7022 : ∀ X0 : G, (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq6934 eq192
    | exact resolve eq192 eq6934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7063 : ∀ X0 X1 X2 : G, (M.op X1 (M.op x y)) = (M.op X0 (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op X2 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 X0 y X2
       have i₂ := eq7022 X0
       grind)
    | exact superpose eq7022 eq181
    | (have j1 := eq7022 X2
       grind)
    | exact resolve eq181 eq7022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq7076 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op X1 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq182 y y x
       have i₂ := eq7022 X0
       grind)
    | exact superpose eq7022 eq182
    | (have j1 := eq7022 X1
       grind)
    | exact resolve eq182 eq7022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7022
  have eq8531 : ∀ X0 X1 : G, (M.op x y) ≠ (M.op X1 (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq7063 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7063
  have eq8619 : ∀ X0 X2 : G, (M.op x y) ≠ (M.op X0 (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op X2 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X2
    first
    | (have i₁ := eq8531 X0 (M.op X0 sF0)
       have i₂ := eq182 X0 sF0 X2
       grind)
    | exact superpose eq182 eq8531
    | (have j0 := eq8531 X2 x
       grind)
    | exact resolve eq8531 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8531
  have eq8638 : ∀ X0 X2 : G, (M.op x y) ≠ (M.op X0 (M.op (M.op x y) y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op X2 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X2
    first
    | exact superpose eq7076 eq8619
    | (have j0 := eq8619 X0 X2
       have j1 := eq7076 X0 X2
       grind)
    | exact resolve eq8619 eq7076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7076 eq8619
  have eq8641 : ∀ X2 : G, (M.op x y) ≠ (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op X2 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq192 eq8638
    | (have j0 := eq8638 x X2
       grind)
    | exact resolve eq8638 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq8638
  have eq10563 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1154 eq115
    | exact resolve eq115 eq1154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154
  have eq10577 : x = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq10563
    | exact resolve eq10563 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10563
  have eq10581 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | exact superpose eq1225 eq10577
    | exact resolve eq10577 eq1225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10577
  have eq13388 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq10581
       grind)
    | exact superpose eq10581 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq10581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10581
  have eq13405 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by grind
  clear eq13388
  have eq13883 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by grind
  clear eq13405
  have eq13890 : x = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq13883
       have r₂ := eq1225
       grind)
    | exact resolve eq13883 eq1225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225 eq13883
  have eq13902 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq789 y y X0
       have i₂ := eq13890
       grind)
    | exact superpose eq13890 eq789
    | (have j0 := eq789 y y x
       grind)
    | exact resolve eq789 eq13890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13905 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op y y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq13902 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13902
  have eq13909 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13905 x
       have i₂ := eq179 x
       grind)
    | exact superpose eq179 eq13905
    | exact resolve eq13905 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13905
  have eq13913 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13909
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13909
    | exact resolve eq13909 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13909
  have eq13916 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6934 eq13913
    | exact resolve eq13913 eq6934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6934 eq13913
  have eq13917 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13916
  have eq13949 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq13917 eq8641
    | (have j0 := eq8641 X0
       grind)
    | (have r₁ := eq8641 x
       have r₂ := eq13917
       grind)
    | exact resolve eq8641 eq13917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8641
  have eq13964 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq13949 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13949
  have eq13965 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq13964 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13964
  have eq17520 : (M.op x y) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq277
       have i₂ := eq1294 (τ (M.op sF2 sF2))
       grind)
    | exact superpose eq1294 eq277
    | (have j1 := eq1294 (τ (M.op (σ x) (σ x)))
       grind)
    | exact resolve eq277 eq1294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277 eq1294
  have eq17555 : (M.op x y) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (M.op (M.op x y) y) = (τ (M.op (σ x) (σ x))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1196 eq17520
    | exact resolve eq17520 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196 eq17520
  have eq17567 : (M.op x y) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (M.op x y) = (τ (M.op (σ x) (σ x))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1218 eq17555
    | exact resolve eq17555 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218 eq17555
  have eq17568 : (M.op x y) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq17567
  have eq17662 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17568 eq14
    | exact resolve eq14 eq17568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17673 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq17662
    | exact resolve eq17662 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17662
  have eq17697 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17673 eq4406
    | exact resolve eq4406 eq17673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4406 eq17673
  have eq17735 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq17697
  have eq17775 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17735
       have r₂ := eq27
       grind)
    | exact resolve eq17735 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17735
  have eq19815 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2138 eq115
    | exact resolve eq115 eq2138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2138
  have eq19829 : x = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq19815
    | exact resolve eq19815 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19815
  have eq19833 : x = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq13890 eq19829
    | exact resolve eq19829 eq13890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13890 eq19829
  have eq21422 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq6884 eq204
    | exact resolve eq204 eq6884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq6884
  have eq21461 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op X0 (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq17775 eq21422
    | exact resolve eq21422 eq17775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17775 eq21422
  have eq22122 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq789 y y X0
       have i₂ := eq19833
       grind)
    | exact superpose eq19833 eq789
    | (have j0 := eq789 y y x
       grind)
    | exact resolve eq789 eq19833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22125 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op y y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq22122 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22122
  have eq22131 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq22125 x
       have i₂ := eq179 x
       grind)
    | exact superpose eq179 eq22125
    | exact resolve eq22125 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq22125
  have eq22140 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq22131
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22131
    | exact resolve eq22131 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22131
  have eq22143 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq13917 eq22140
    | exact resolve eq22140 eq13917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13917 eq22140
  have eq22144 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq13965 eq22143
    | (have j1 := eq13965 (M.op x y)
       grind)
    | exact resolve eq22143 eq13965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13965 eq22143
  have eq22145 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq22144
  have eq24826 : ∀ X0 : G, (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op X0 (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq21461 eq184
    | (have j1 := eq21461 X0
       grind)
    | exact resolve eq184 eq21461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24836 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op X1 (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq21461 eq16
    | (have j1 := eq21461 X1
       grind)
    | exact resolve eq16 eq21461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24869 : ∀ X0 X1 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op X1 (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq21461 eq24836
    | (have j0 := eq24836 X0 X1
       have j1 := eq21461 X1
       grind)
    | exact resolve eq24836 eq21461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21461 eq24836
  have eq24875 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1342 eq24826
    | (have j0 := eq24826 X0
       grind)
    | exact resolve eq24826 eq1342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342 eq24826
  have eq25012 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24875 eq17568
    | exact resolve eq17568 eq24875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24875
  have eq25015 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq25012
  have eq25072 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29 eq25015
    | exact resolve eq25015 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25015
  have eq25073 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq25072
  have eq25853 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq22145
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq22145
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq22145 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25895 : x ≠ (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq22145
  have eq25906 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq25853
  have eq25927 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq822 (M.op x y)
       grind)
    | (have r₁ := eq25906
       have r₂ := eq822 (M.op x y)
       grind)
    | exact resolve eq25906 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25906
  have eq28168 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op X0 (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24869 eq26
    | (have j1 := eq24869 (σ x) X0
       grind)
    | exact resolve eq26 eq24869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24869
  have eq28210 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq28168 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28168
  have eq28377 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28210 eq17568
    | exact resolve eq17568 eq28210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17568 eq28210
  have eq28380 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28377
  have eq28439 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq28380
    | exact resolve eq28380 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28380
  have eq28440 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq28439
  have eq28481 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28440 eq763
    | (have r₁ := eq763
       have r₂ := eq28440
       grind)
    | exact resolve eq763 eq28440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq28483 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq28481
  have eq28533 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28483 eq152
    | exact resolve eq152 eq28483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq28483
  have eq28544 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq28533
    | exact resolve eq28533 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28533
  have eq28559 : (τ (σ x)) = (k (τ (σ x)) y) ∨ x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28544 eq298
    | exact resolve eq298 eq28544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28544
  have eq28643 : x = (k x y) ∨ x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq28559
    | exact resolve eq28559 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28559
  have eq28644 : x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq28643
  have eq28675 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq780
       have i₂ := eq28644
       grind)
    | exact superpose eq28644 eq780
    | exact resolve eq780 eq28644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780 eq28644
  have eq28680 : x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq28675
  have eq28692 : x = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28680
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq28680
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq28680 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28704 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq187 y
       have i₂ := eq28680
       grind)
    | exact superpose eq28680 eq187
    | exact resolve eq187 eq28680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28722 : x = (k y y) ∨ x = y ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq28680
       grind)
    | exact superpose eq28680 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq28680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28724 : ∀ X0 : G, (M.op x y) = (M.op X0 x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq28680
       grind)
    | exact superpose eq28680 eq16
    | exact resolve eq16 eq28680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28737 : ∀ X0 X1 : G, (M.op (M.op X0 y) y) = (M.op X1 (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1502 y y X0 X1
       have i₂ := eq28680
       grind)
    | exact superpose eq28680 eq1502
    | exact resolve eq1502 eq28680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1502 eq28680
  have eq28739 : x = (k y y) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq28722
  have eq28748 : x = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq28692
  have eq28754 : ∀ X0 X1 : G, (M.op (M.op X0 y) y) = (M.op X1 (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq28737 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28737
    | (have j0 := eq28737 X0 X1
       grind)
    | exact resolve eq28737 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28737
  have eq28767 : ∀ X0 : G, (M.op x y) = (M.op X0 x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq28724 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28724
    | (have j0 := eq28724 X0
       grind)
    | exact resolve eq28724 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28724
  have eq28778 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28704
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28704
    | exact resolve eq28704 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28704
  have eq28780 : x = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28739 eq28748
    | exact resolve eq28748 eq28739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28739 eq28748
  have eq28781 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op X1 (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq28754 x X1
       have i₂ := eq187 x
       grind)
    | (have i₁ := eq28754 x X1
       have i₂ := eq187 X1
       grind)
    | exact superpose eq187 eq28754
    | (have j0 := eq28754 x X1
       grind)
    | exact resolve eq28754 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq28754
  have eq28798 : x = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28767 eq28780
    | exact resolve eq28780 eq28767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28780
  have eq28799 : x = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq28798
  have eq28800 : ∀ X1 : G, (M.op x y) = (M.op X1 (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq28778 eq28781
    | exact resolve eq28781 eq28778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28778 eq28781
  have eq29121 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq28799
       grind)
    | exact superpose eq28799 eq40
    | exact resolve eq40 eq28799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29138 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29121
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29121
    | exact resolve eq29121 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29121
  have eq29141 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29138
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29138
    | exact resolve eq29138 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29138
  have eq29344 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29141 eq789
    | (have j0 := eq789 (σ y) (σ y) x
       grind)
    | exact resolve eq789 eq29141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq29347 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq29344 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29344
  have eq29348 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq180 eq29347
    | exact resolve eq29347 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq29347
  have eq29353 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq29348
    | exact resolve eq29348 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29348
  have eq29357 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28440 eq29353
    | exact resolve eq29353 eq28440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28440 eq29353
  have eq29358 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq29357
  have eq29386 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29358 eq298
    | exact resolve eq298 eq29358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29405 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29358 eq184
    | exact resolve eq184 eq29358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29358
  have eq29459 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29141 eq29405
    | exact resolve eq29405 eq29141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29141 eq29405
  have eq29460 : y = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq29386
    | exact resolve eq29386 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29386
  have eq29469 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28799 eq29460
    | exact resolve eq29460 eq28799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29460
  have eq29483 : (k y y) = (τ (k (σ x) (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29459 eq115
    | exact resolve eq115 eq29459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29650 : (k x x) = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq97 eq29483
    | exact resolve eq29483 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq29483
  have eq29672 : x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28799 eq29650
    | exact resolve eq29650 eq28799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28799 eq29650
  have eq29688 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq29469
       grind)
    | exact superpose eq29469 eq18
    | exact resolve eq18 eq29469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29705 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19833
       have i₂ := eq29469
       grind)
    | exact superpose eq29469 eq19833
    | exact resolve eq19833 eq29469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19833 eq29469
  have eq29710 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have r₁ := eq29705
       have r₂ := eq25895
       grind)
    | exact resolve eq29705 eq25895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25895 eq29705
  have eq29722 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28800 eq29688
    | (have j1 := eq28800 x
       grind)
    | exact resolve eq29688 eq28800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28800 eq29688
  have eq29723 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq29722
  have eq29724 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq25927 eq29710
    | exact resolve eq29710 eq25927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25927 eq29710
  have eq29727 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25073 eq29724
    | exact resolve eq29724 eq25073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25073 eq29724
  have eq29728 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq29727
  have eq29747 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29723 eq16
    | exact resolve eq16 eq29723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29750 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29723 eq175
    | exact resolve eq175 eq29723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq29755 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29723 eq832
    | (have j0 := eq832 (M.op x y) x x
       grind)
    | exact resolve eq832 eq29723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq30672 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq820 x x
       have i₂ := eq29672
       grind)
    | exact superpose eq29672 eq820
    | (have j0 := eq820 x x
       grind)
    | (have r₁ := eq820 x x
       have r₂ := eq29672
       grind)
    | exact resolve eq820 eq29672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820 eq29672
  have eq30673 : x ≠ x ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq30672
  have eq30674 : x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq30673
  have eq30691 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28767 eq30674
    | exact resolve eq30674 eq28767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28767 eq30674
  have eq30692 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq30691
  have eq30703 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq30692
       grind)
    | exact superpose eq30692 eq24
    | exact resolve eq24 eq30692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30712 : (M.op (M.op x y) (M.op x y)) = (k (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq222
       have i₂ := eq30692
       grind)
    | exact superpose eq30692 eq222
    | exact resolve eq222 eq30692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30726 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq30703
    | exact resolve eq30703 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30703
  have eq31094 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op X0 (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq29747 X0
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq29747
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq29747 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29747
  have eq31195 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op X0 (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq31094 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31094
  have eq38761 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq31195 eq29755
    | exact resolve eq29755 eq31195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29755 eq31195
  have eq38826 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq38761
  have eq38858 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq38826
       have r₂ := eq13 (k (M.op x y) (M.op x y)) (M.op x y)
       grind)
    | (have r₁ := eq38826
       have r₂ := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq38826 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38826
  have eq38902 : (k (M.op x y) (M.op x y)) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38858 eq30712
    | exact resolve eq30712 eq38858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30712
  have eq38924 : (k (M.op x y) (M.op x y)) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38858 eq29750
    | exact resolve eq29750 eq38858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29750 eq38858
  have eq38961 : (k (M.op x y) (M.op x y)) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq38924
  have eq38973 : (k (M.op x y) (M.op x y)) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq38902
  have eq39078 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29728 eq38961
    | exact resolve eq38961 eq29728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29728
  have eq39161 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq39078
  have eq39179 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29723 eq39161
    | exact resolve eq39161 eq29723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39161
  have eq39180 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq39179
  have eq39403 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39180 eq27
    | exact resolve eq27 eq39180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39180
  have eq39415 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq39403
       have r₂ := eq30726
       grind)
    | exact resolve eq39403 eq30726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39403
  have eq54470 : (σ (k (M.op x y) (M.op x y))) ≠ (σ (k (M.op x y) (M.op x y))) ∨ (σ (k (M.op x y) (M.op x y))) = (M.op (σ (k (M.op x y) (M.op x y))) (σ (k (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38973 eq857
    | (have j0 := eq857 (k (M.op x y) (M.op x y))
       grind)
    | exact resolve eq857 eq38973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38973
  have eq54568 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (k (M.op x y) (M.op x y))) (σ (k (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by grind
  clear eq54470
  have eq54634 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq41 eq54568
    | exact resolve eq54568 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq54568
  have eq54667 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq54634
    | exact resolve eq54634 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54634
  have eq54679 : (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30726 eq54667
    | exact resolve eq54667 eq30726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30726 eq54667
  have eq54716 : (k (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq54679 eq823
    | exact resolve eq823 eq54679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823 eq54679
  have eq55678 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq39415 eq54716
    | exact resolve eq54716 eq39415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54716
  have eq55770 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq55678
  have eq55799 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq55770
    | exact resolve eq55770 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55770
  have eq55823 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq39415 eq55799
    | exact resolve eq55799 eq39415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55799
  have eq71769 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq55823 eq16
    | exact resolve eq16 eq55823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71831 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq55823 eq71769
    | exact resolve eq71769 eq55823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55823 eq71769
  have eq72384 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq71831 eq26
    | (have j1 := eq71831 (σ x)
       grind)
    | exact resolve eq26 eq71831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71831
  have eq72492 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq39415 eq72384
    | exact resolve eq72384 eq39415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39415 eq72384
  have eq72493 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq72492
  have eq72528 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq72493 eq115
    | exact resolve eq115 eq72493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72493
  have eq72589 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq72528
    | exact resolve eq72528 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72528
  have eq72596 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29459 eq72589
    | exact resolve eq72589 eq29459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29459 eq72589
  have eq72646 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq72596 eq38961
    | exact resolve eq38961 eq72596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38961 eq72596
  have eq72704 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq72646
  have eq72755 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29723 eq72704
    | exact resolve eq72704 eq29723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29723 eq72704
  have eq72756 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq72755
  have eq75346 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq72756 eq31
    | exact resolve eq31 eq72756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72756
  have eq75599 : x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq75346
    | exact resolve eq75346 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq75346
  have eq75623 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30692 eq75599
    | exact resolve eq75599 eq30692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30692 eq75599
  have eq75624 : x = (M.op x y) := by grind
  clear eq75623
  have eq75632 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq75624
       grind)
    | exact superpose eq75624 eq18
    | exact resolve eq18 eq75624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq75633 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq75624
       grind)
    | exact superpose eq75624 eq22
    | exact resolve eq22 eq75624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq75667 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq75633 eq20
    | exact resolve eq20 eq75633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75957 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq75632 eq222
    | exact resolve eq222 eq75632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq76292 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq75957 eq857
    | (have j0 := eq857 (M.op x y)
       grind)
    | exact resolve eq857 eq75957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857 eq75957
  have eq76303 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq76292
  have eq76308 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq76303
    | exact resolve eq76303 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76303
  have eq76311 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq75667 eq76308
    | exact resolve eq76308 eq75667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76308
  have eq76391 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq76311 eq2144
    | exact resolve eq2144 eq76311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2144
  have eq76437 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq76311 eq182
    | exact resolve eq182 eq76311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq76446 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op X1 (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq76311 eq1501
    | exact resolve eq1501 eq76311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76456 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq76391
  have eq76466 : ∀ X0 X1 : G, (σ x) = (M.op X0 (M.op X1 (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq76311 eq76446
    | exact resolve eq76446 eq76311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76446
  have eq76471 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq76311 eq76437
    | exact resolve eq76437 eq76311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76311 eq76437
  have eq76478 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq76456
       have i₂ := eq75624
       grind)
    | exact superpose eq75624 eq76456
    | exact resolve eq76456 eq75624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75624 eq76456
  have eq79290 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (k X0 (σ (M.op y y))) ∨ (M.op y y) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (M.op y y)
       have i₂ := eq854 (τ X0)
       grind)
    | exact superpose eq854 eq34
    | exact resolve eq34 eq854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq79297 : (σ (M.op (M.op x y) y)) = (k (σ y) (σ (M.op y y))) ∨ (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq36 (M.op y y)
       have i₂ := eq854 y
       grind)
    | exact superpose eq854 eq36
    | exact resolve eq36 eq854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq79312 : (σ (M.op x y)) = (k (σ y) (σ (M.op y y))) ∨ (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq75632 eq79297
    | exact resolve eq79297 eq75632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79297
  have eq79316 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op y y))) ∨ (M.op y y) = (M.op (M.op x y) y) := by
    intro X0
    first
    | exact superpose eq75632 eq79290
    | exact resolve eq79290 eq75632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79290
  have eq79333 : (σ (M.op x y)) = (k (σ y) (σ (M.op y y))) ∨ (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq20 eq79312
    | exact resolve eq79312 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79312
  have eq79337 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op y y))) ∨ (M.op y y) = (M.op (M.op x y) y) := by
    intro X0
    first
    | exact superpose eq20 eq79316
    | (have j0 := eq79316 X0
       grind)
    | exact resolve eq79316 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79316
  have eq79349 : (σ x) = (k (σ y) (σ (M.op y y))) ∨ (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq75667 eq79333
    | exact resolve eq79333 eq75667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79333
  have eq79352 : ∀ X0 : G, (σ x) = (k X0 (σ (M.op y y))) ∨ (M.op y y) = (M.op (M.op x y) y) := by
    intro X0
    first
    | exact superpose eq75667 eq79337
    | exact resolve eq79337 eq75667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79337
  have eq79358 : (σ x) = (k (σ y) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq75632 eq79349
    | exact resolve eq79349 eq75632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79349
  have eq79361 : ∀ X0 : G, (σ x) = (k X0 (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq75632 eq79352
    | (have j0 := eq79352 X0
       grind)
    | exact resolve eq79352 eq75632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75632 eq79352
  have eq86619 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq213
       have i₂ := eq76478
       grind)
    | exact superpose eq76478 eq213
    | exact resolve eq213 eq76478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq76478
  have eq86740 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq86619
    | exact resolve eq86619 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86619
  have eq86774 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq75667 eq86740
    | exact resolve eq86740 eq75667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86740
  have eq86854 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq86774 eq781
    | exact resolve eq781 eq86774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781 eq86774
  have eq86861 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq86854
  have eq87220 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X1 (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq86861 eq1501
    | exact resolve eq1501 eq86861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86861
  have eq87254 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq76466 eq87220
    | exact resolve eq87220 eq76466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87220
  have eq87302 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq87254
    | exact resolve eq87254 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87254
  have eq87303 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq87302
  have eq87342 : ∀ X0 : G, (k X0 (M.op (σ y) (σ y))) = X0 ∨ (M.op (σ y) (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq87303 eq766
    | exact resolve eq766 eq87303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq87359 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq87303
  have eq92870 : (σ x) = (k (σ y) (σ (k y y))) ∨ (M.op x y) = (k y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq79358
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq79358
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq79358 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79358
  have eq92879 : (σ x) = (k (σ y) (σ (k y y))) ∨ (M.op x y) = (k y y) ∨ y = (M.op y y) := by grind
  clear eq92870
  have eq92888 : (σ x) = (k (σ y) (k (σ y) (σ y))) ∨ (M.op x y) = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq92879
       have i₂ := eq40 y
       grind)
    | exact superpose eq40 eq92879
    | exact resolve eq92879 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92879
  have eq92893 : (σ x) = (k (σ y) (k (σ y) (σ y))) ∨ (M.op x y) = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq92888
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq92888
    | exact resolve eq92888 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92888
  have eq92938 : (σ x) = (M.op (σ (M.op y y)) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq184 (σ (M.op y y))
       have i₂ := eq79361 (M.op (σ (M.op y y)) (σ (M.op y y)))
       grind)
    | exact superpose eq79361 eq184
    | exact resolve eq184 eq79361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79361
  have eq117520 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq87342 eq107
    | (have j1 := eq87342 (σ y)
       grind)
    | exact resolve eq107 eq87342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq87342
  have eq117535 : y = (k y (τ (M.op (σ y) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq117520
    | exact resolve eq117520 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117520
  have eq121791 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op (σ x) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq1501 X0 (σ (M.op y y)) (σ (M.op y y)) x
       have i₂ := eq92938
       grind)
    | exact superpose eq92938 eq1501
    | exact resolve eq1501 eq92938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1501 eq92938
  have eq121811 : (σ x) = (M.op (σ x) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq76466 eq121791
    | exact resolve eq121791 eq76466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76466 eq121791
  have eq140816 : y = (k y (τ (k (σ y) (σ y)))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq117535
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq117535
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq117535 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117535
  have eq140826 : y = (k y (τ (k (σ y) (σ y)))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq140816
  have eq140842 : y = (k y (τ (k (σ y) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq822 (σ y)
       grind)
    | (have r₁ := eq140826
       have r₂ := eq822 (σ y)
       grind)
    | exact resolve eq140826 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140826
  have eq140852 : y = (k y (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq115 eq140842
    | exact resolve eq140842 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq140842
  have eq140871 : (σ y) = (k (σ y) (σ (k y y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq36 (k y y)
       have i₂ := eq140852
       grind)
    | exact superpose eq140852 eq36
    | exact resolve eq36 eq140852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq140852
  have eq140877 : (σ y) = (k (σ y) (k (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq140871
       have i₂ := eq40 y
       grind)
    | exact superpose eq40 eq140871
    | exact resolve eq140871 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140871
  have eq140882 : (σ y) = (k (σ y) (k (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq140877
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq140877
    | exact resolve eq140877 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140877
  have eq152298 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq92893 eq140882
    | exact resolve eq140882 eq92893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92893 eq140882
  have eq152311 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq152298
       have r₂ := eq87359
       grind)
    | exact resolve eq152298 eq87359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152298
  have eq678138 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq152311 eq298
    | exact resolve eq298 eq152311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298 eq152311
  have eq678414 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq31 eq678138
    | exact resolve eq678138 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq678138
  have eq678440 : (M.op x y) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq822 y
       grind)
    | (have r₁ := eq678414
       have r₂ := eq822 y
       grind)
    | exact resolve eq678414 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822 eq678414
  have eq678498 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq678440
       grind)
    | exact superpose eq678440 eq40
    | exact resolve eq40 eq678440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq678440
  have eq678627 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq678498
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq678498
    | exact resolve eq678498 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678498
  have eq678657 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq678627
    | exact resolve eq678627 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq678627
  have eq678676 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq75667 eq678657
    | exact resolve eq678657 eq75667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678657
  have eq678798 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq678676 eq2892
    | (have j0 := eq2892 (σ y) (σ y) x
       grind)
    | exact resolve eq2892 eq678676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2892
  have eq678817 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq678798 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678798
  have eq678835 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq76471 eq678817
    | exact resolve eq678817 eq76471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76471 eq678817
  have eq678877 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq678835
    | exact resolve eq678835 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678835
  have eq678878 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq678877
  have eq679024 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq678878 eq184
    | exact resolve eq184 eq678878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq678878
  have eq679225 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq678676 eq679024
    | exact resolve eq679024 eq678676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678676 eq679024
  have eq679262 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq679225
       have r₂ := eq87359
       grind)
    | exact resolve eq679225 eq87359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679225
  have eq679335 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq121811
       have i₂ := eq679262
       grind)
    | exact superpose eq679262 eq121811
    | exact resolve eq121811 eq679262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121811 eq679262
  have eq679542 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq679335
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq679335
    | exact resolve eq679335 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679335
  have eq679583 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq679542
    | exact resolve eq679542 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq679542
  have eq679584 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq679583
  have eq679624 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq679584 eq27
    | exact resolve eq27 eq679584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679584
  have eq679740 : y = (M.op x y) := by
    first
    | (have r₁ := eq679624
       have r₂ := eq75667
       grind)
    | exact resolve eq679624 eq75667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679624
  have eq679756 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq679740
       grind)
    | exact superpose eq679740 eq24
    | exact resolve eq24 eq679740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq679740
  have eq680154 : (σ x) = (σ y) := by
    first
    | exact superpose eq75633 eq679756
    | exact resolve eq679756 eq75633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75633 eq679756
  have eq680510 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq680154 eq87359
    | (have r₁ := eq87359
       have r₂ := eq680154
       grind)
    | exact resolve eq87359 eq680154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87359 eq680154
  have eq680756 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq680510
  have eq681130 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq680756 eq27
    | exact resolve eq27 eq680756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq680756
  have eq681203 : False := by grind
  exact eq681203
