import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4428`: `x ◇ (x ◇ y) = (z ◇ w) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_y_pyx_pxx_pyx_Equation4428 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4428 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4428.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X1) := by
    intro X0 X1 X2 X3
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
  have eq50 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) (M.op X3 X2)) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 X3 (M.op X3 X2) X4 X5
       have i₂ := eq14 X3 X2 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X3 X2) ∨ (M.op (M.op X0 X1) X2) = (k (M.op X3 X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X0 X1) X0
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq13
    | (have r₁ := eq13 (M.op (M.op X2 X3) X1) (M.op X2 X3)
       have r₂ := eq14 (M.op X2 X3) X1 X2 X3
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq76 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq36 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq36
    | exact resolve eq36 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq81 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq82 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq74
    | (have j0 := eq74 X0 (σ X1)
       grind)
    | exact resolve eq74 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq80
       have i₂ := eq74 y x
       grind)
    | exact superpose eq74 eq80
    | (have j1 := eq74 x x
       grind)
    | exact resolve eq80 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq101
    | exact resolve eq101 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq108 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq81
       grind)
    | exact superpose eq81 eq16
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq82 eq16
    | exact resolve eq16 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq118 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) ≠ (M.op X0 (M.op X0 (M.op X1 X2))) ∨ (M.op (M.op X1 X2) X3) = X3 ∨ (k X3 (M.op X1 X2)) = (M.op X3 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 (M.op X1 X2)
       have i₂ := eq14 X0 (M.op X1 X2) X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X3 (M.op X1 X2)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq176 : (σ (k (k y y) y)) = (k (k (σ y) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq40 (k y y)
       have i₂ := eq81
       grind)
    | exact superpose eq81 eq40
    | exact resolve eq40 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq208 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X1) X2)) = (M.op (M.op x y) (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X3 (M.op X3 X2)
       have i₂ := eq14 X3 X2 X0 X1
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq56 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq56
    | (have j0 := eq56 x y
       grind)
    | exact resolve eq56 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 x X2
       have i₂ := eq14 x X2 X0 X1
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x (M.op x y))) := by
    first
    | exact superpose eq210 eq56
    | exact resolve eq56 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X1 : G, (M.op (M.op x y) X1) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X1
    first
    | (have i₁ := eq57 x X1
       have i₂ := eq56 x X1
       grind)
    | exact superpose eq56 eq57
    | exact resolve eq57 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq228 : ∀ X0 : G, (M.op (M.op x y) X0) ≠ X0 ∨ (M.op (M.op x y) X0) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq225 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | exact resolve eq13 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq16
    | exact resolve eq16 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k y (τ X0))
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq397 : (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ (M.op x (M.op x y)) = (k (M.op x (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq222 eq13
    | (have r₁ := eq13 (M.op x (M.op x y)) (M.op x y)
       have r₂ := eq222
       grind)
    | exact resolve eq13 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq399 : (M.op x (M.op x y)) = (k (M.op x (M.op x y)) (M.op x y)) := by grind
  clear eq397
  have eq463 : ∀ X2 X3 X4 X5 : G, (M.op (M.op X4 X5) (M.op X3 X2)) = (M.op X3 (M.op (M.op x y) X2)) := by
    intro X2 X3 X4 X5
    first
    | (have i₁ := eq50 x x X2 X3 X4 X5
       have i₂ := eq212 x x X2
       grind)
    | (have i₁ := eq50 x y X2 X3 X4 X5
       have i₂ := eq212 x x X2
       grind)
    | exact superpose eq212 eq50
    | (have j0 := eq50 x y X2 X3 X4 X5
       grind)
    | exact resolve eq50 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq464 : ∀ X2 X3 : G, (M.op (M.op x y) (M.op X3 X2)) = (M.op X3 (M.op (M.op x y) X2)) := by
    intro X2 X3
    first
    | (have i₁ := eq463 X2 X3 x x
       have i₂ := eq212 x x (M.op X3 X2)
       grind)
    | (have i₁ := eq463 X2 X3 x y
       have i₂ := eq212 x x (M.op X3 X2)
       grind)
    | exact superpose eq212 eq463
    | (have j0 := eq463 X2 X3 x y
       grind)
    | exact resolve eq463 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq472 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq278 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq278
    | exact resolve eq278 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq528 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 (M.op (M.op x y) X1)) ∨ (M.op X0 (M.op (M.op x y) X1)) = (k (M.op X0 X1) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq464 eq13
    | exact resolve eq13 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq683 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq102 eq74
    | (have j0 := eq74 x (σ x)
       grind)
    | exact resolve eq74 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq684 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq683
    | exact resolve eq683 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq687 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq684
       have r₂ := eq27
       grind)
    | exact resolve eq684 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq691 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq687 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq687
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq687
       grind)
    | exact resolve eq13 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq695 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq691
  have eq700 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq695 eq49
    | exact resolve eq49 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq695
  have eq704 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq700
    | exact resolve eq700 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq700
  have eq707 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq74 x x
       have i₂ := eq704
       grind)
    | exact superpose eq704 eq74
    | (have j0 := eq74 x x
       grind)
    | exact resolve eq74 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq708 : x = (M.op x x) := by grind
  clear eq707
  have eq712 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq212 x x X0
       have i₂ := eq708
       grind)
    | exact superpose eq708 eq212
    | exact resolve eq212 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq714 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq708
       grind)
    | exact superpose eq708 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq708
       grind)
    | exact resolve eq13 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq718 : x = (k x x) := by grind
  clear eq714
  have eq724 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq718
       grind)
    | exact superpose eq718 eq43
    | exact resolve eq43 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq728 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq724
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq724
    | exact resolve eq724 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq746 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq728 eq74
    | (have j0 := eq74 x (σ x)
       grind)
    | exact resolve eq74 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq747 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq746
  have eq754 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq747 eq212
    | exact resolve eq212 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq800 : ∀ X0 X1 : G, (M.op (M.op x y) (σ X0)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X1) (σ X0)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq56
    | (have j1 := eq88 X0 X1
       grind)
    | exact resolve eq56 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq804 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq88 X0 X0
       grind)
    | exact superpose eq88 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq88 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq12 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq805 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq88 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq806 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq804 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq804 X0 (σ X0)
       have r₂ := eq12 X0 (σ X0)
       grind)
    | (have r₁ := eq804 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq804 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq856 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq712 eq210
    | exact resolve eq210 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq873 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq856
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq856
    | exact resolve eq856 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq885 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq873 eq399
    | exact resolve eq399 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq894 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) ≠ (M.op (M.op x y) X2) ∨ (M.op (M.op X0 X1) X2) = (k (M.op X3 X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq69 X0 X1 X2 X3
       have i₂ := eq212 X0 X1 X2
       grind)
    | (have i₁ := eq69 x y X2 X3
       have i₂ := eq212 X0 X1 X2
       grind)
    | exact superpose eq212 eq69
    | (have j0 := eq69 x y X2 X3
       grind)
    | (have r₁ := eq69 X0 X1 X2 (M.op x y)
       have r₂ := eq212 X0 X1 X2
       grind)
    | (have r₁ := eq69 x y X2 (M.op X0 X1)
       have r₂ := eq212 X0 X1 X2
       grind)
    | exact resolve eq69 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq895 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) ≠ (M.op x X2) ∨ (M.op (M.op X0 X1) X2) = (k (M.op X3 X2) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq712 eq894
    | (have j0 := eq894 X0 X1 X2 X3
       grind)
    | (have r₁ := eq894 X0 X1 X0 x
       have r₂ := eq712 X0
       grind)
    | exact resolve eq894 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq896 : ∀ X2 X3 : G, (k (M.op X3 X2) X3) = (M.op (M.op x y) X2) ∨ (M.op X3 X2) ≠ (M.op x X2) := by
    intro X2 X3
    first
    | (have i₁ := eq895 x x X2 X3
       have i₂ := eq212 x x X2
       grind)
    | (have i₁ := eq895 x y X2 X3
       have i₂ := eq212 x x X2
       grind)
    | exact superpose eq212 eq895
    | (have j0 := eq895 x y X2 X3
       grind)
    | exact resolve eq895 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq897 : ∀ X2 X3 : G, (M.op X3 X2) ≠ (M.op x X2) ∨ (k (M.op X3 X2) X3) = (M.op x X2) := by
    intro X2 X3
    first
    | exact superpose eq712 eq896
    | (have j0 := eq896 X2 X3
       grind)
    | (have r₁ := eq896 x (M.op x y)
       have r₂ := eq712 x
       grind)
    | exact resolve eq896 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq899 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq885 eq132
    | exact resolve eq132 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885
  have eq904 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq899
    | exact resolve eq899 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq914 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op x X1) ∨ (M.op x X1) = (k (M.op X0 (M.op X0 X1)) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq897 X1 (M.op X2 X3)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq897
    | exact resolve eq897 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq932 : ∀ X0 : G, (M.op (M.op x y) X0) ≠ (M.op x X0) ∨ (M.op x X0) = (k (M.op (M.op x y) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq225 eq897
    | (have j0 := eq897 X0 (M.op x y)
       grind)
    | exact resolve eq897 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225 eq897
  have eq946 : ∀ X0 : G, (M.op x X0) = (k (M.op (M.op x y) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq932 X0
       grind)
    | (have r₁ := eq932 X0
       have r₂ := eq712 X0
       grind)
    | exact resolve eq932 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932
  have eq958 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x y) X1) ≠ (M.op x X1) ∨ (M.op x X1) = (k (M.op X0 (M.op X0 X1)) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq914 X0 X1 X2 X3
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq914
    | (have j0 := eq914 X0 X1 X2 X3
       grind)
    | exact resolve eq914 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914
  have eq965 : ∀ X0 : G, (M.op x X0) = (k (M.op x X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq712 eq946
    | exact resolve eq946 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq973 : ∀ X0 X1 X2 X3 : G, (M.op x X1) = (k (M.op X0 (M.op X0 X1)) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq958 X0 X1 X2 X3
       grind)
    | (have r₁ := eq958 X0 X0 X2 X3
       have r₂ := eq712 X0
       grind)
    | exact resolve eq958 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958
  have eq983 : ∀ X1 X2 X3 : G, (M.op x X1) = (k (M.op (M.op x y) X1) (M.op X2 X3)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq973 x X1 X2 X3
       have i₂ := eq56 x X1
       grind)
    | exact superpose eq56 eq973
    | exact resolve eq973 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973
  have eq991 : ∀ X1 X2 X3 : G, (M.op x X1) = (k (M.op x X1) (M.op X2 X3)) := by
    intro X1 X2 X3
    first
    | exact superpose eq712 eq983
    | exact resolve eq983 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983
  have eq1008 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq904 eq74
    | (have j0 := eq74 x (σ (M.op x y))
       grind)
    | exact resolve eq74 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1009 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq1008
  have eq1029 : ∀ X1 X2 X3 : G, (M.op X1 X2) ≠ (M.op (M.op x y) (M.op X1 X2)) ∨ (M.op (M.op X1 X2) X3) = X3 ∨ (k X3 (M.op X1 X2)) = (M.op X3 X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq118 x X1 X2 X3
       have i₂ := eq56 x (M.op X1 X2)
       grind)
    | exact superpose eq56 eq118
    | (have j0 := eq118 x X1 X2 X3
       grind)
    | exact resolve eq118 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq1030 : ∀ X1 X2 X3 : G, (M.op X1 X2) ≠ (M.op x (M.op X1 X2)) ∨ (M.op (M.op X1 X2) X3) = X3 ∨ (k X3 (M.op X1 X2)) = (M.op X3 X3) := by
    intro X1 X2 X3
    first
    | exact superpose eq712 eq1029
    | (have j0 := eq1029 X1 X2 X3
       grind)
    | exact resolve eq1029 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
  have eq1031 : ∀ X1 X2 X3 : G, (M.op (M.op x y) X3) = X3 ∨ (M.op X1 X2) ≠ (M.op x (M.op X1 X2)) ∨ (k X3 (M.op X1 X2)) = (M.op X3 X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq1030 X1 X2 X3
       have i₂ := eq212 X1 X2 X3
       grind)
    | (have i₁ := eq1030 x y X2
       have i₂ := eq212 x X1 X2
       grind)
    | exact superpose eq212 eq1030
    | (have j0 := eq1030 X1 X2 X3
       grind)
    | exact resolve eq1030 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030
  have eq1032 : ∀ X1 X2 X3 : G, (M.op X1 X2) ≠ (M.op x (M.op X1 X2)) ∨ (M.op x X3) = X3 ∨ (k X3 (M.op X1 X2)) = (M.op X3 X3) := by
    intro X1 X2 X3
    first
    | exact superpose eq712 eq1031
    | (have j0 := eq1031 X1 X2 X3
       grind)
    | exact resolve eq1031 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031
  have eq1036 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq1009 eq212
    | exact resolve eq212 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009
  have eq1042 : ∀ X0 : G, (M.op x X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq712 eq1036
    | exact resolve eq1036 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq1055 : ∀ X0 : G, (M.op x y) ≠ (M.op x (M.op x y)) ∨ (M.op x X0) = X0 ∨ (M.op X0 X0) = (k X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1032 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1032
    | (have j0 := eq1032 x y X0
       grind)
    | exact resolve eq1032 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1073 : ∀ X0 X1 : G, (M.op (M.op x y) X0) ≠ (M.op x X0) ∨ (M.op x X1) = X1 ∨ (M.op X1 X1) = (k X1 (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1032 x X0 X1
       have i₂ := eq56 x X0
       grind)
    | exact superpose eq56 eq1032
    | (have j0 := eq1032 x X0 X1
       grind)
    | exact resolve eq1032 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq1032
  have eq1074 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op x X0)) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1073 X0 X1
       grind)
    | (have r₁ := eq1073 X0 X1
       have r₂ := eq712 X0
       grind)
    | exact resolve eq1073 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073
  have eq1080 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x y)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1055 X0
       grind)
    | (have r₁ := eq1055 X0
       have r₂ := eq873
       grind)
    | exact resolve eq1055 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873 eq1055
  have eq1265 : ∀ X0 : G, (k X0 (M.op x y)) ≠ X0 ∨ (k X0 (M.op x y)) = (k X0 X0) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq1080 X0
       grind)
    | (have i₁ := eq13 X0 x
       have i₂ := eq1080 X0
       grind)
    | exact superpose eq1080 eq13
    | (have j1 := eq1080 X0
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq1080 X0
       grind)
    | exact resolve eq13 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1276 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (k (M.op X0 X1) (M.op x y)) ∨ (M.op X0 X1) = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq212 X0 X1 (M.op X0 X1)
       have i₂ := eq1080 (M.op X0 X1)
       grind)
    | exact superpose eq1080 eq212
    | (have j1 := eq1080 (M.op X0 X1)
       grind)
    | exact resolve eq212 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1278 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ X0) (M.op x y)) ∨ (σ X0) = (k (σ X0) (M.op x y)) ∨ (σ X0) = (M.op x (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq88 x x
       have i₂ := eq1080 (σ x)
       grind)
    | exact superpose eq1080 eq88
    | (have j1 := eq1080 (σ X0)
       grind)
    | exact resolve eq88 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1291 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op x y)) = (M.op x (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq712 eq1276
    | (have j0 := eq1276 X0 X1
       grind)
    | exact resolve eq1276 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276
  have eq1387 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X0 X1)) = (k (M.op X0 X1) (M.op x X2)) ∨ (M.op X0 X1) = (M.op x (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq212 X0 X1 (M.op X0 X1)
       have i₂ := eq1074 X2 (M.op X0 X1)
       grind)
    | exact superpose eq1074 eq212
    | (have j1 := eq1074 X0 (M.op X0 X1)
       grind)
    | exact resolve eq212 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1404 : ∀ X0 X1 X2 : G, (M.op x (M.op X0 X1)) = (k (M.op X0 X1) (M.op x X2)) ∨ (M.op X0 X1) = (M.op x (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq712 eq1387
    | (have j0 := eq1387 X0 X1 X2
       grind)
    | exact resolve eq1387 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1387
  have eq1512 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq712 eq754
    | exact resolve eq754 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq1653 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq26 eq1512
    | (have j0 := eq1512 (σ y)
       grind)
    | exact resolve eq1512 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1664 : ∀ X0 : G, (M.op x X0) ≠ X0 ∨ (k X0 (σ x)) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq1512 eq13
    | (have j0 := eq13 X0 x
       grind)
    | exact resolve eq13 eq1512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1724 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (σ x) (σ y))) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | exact superpose eq1653 eq1074
    | (have j0 := eq1074 X0 X0
       grind)
    | exact resolve eq1074 eq1653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074
  have eq1725 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq1653 eq991
    | exact resolve eq991 eq1653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991
  have eq1726 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1653 eq965
    | exact resolve eq965 eq1653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965
  have eq2470 : ∀ X0 : G, (M.op x X0) ≠ X0 ∨ (k X0 (σ (M.op x y))) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq1042 eq13
    | (have j0 := eq13 X0 x
       grind)
    | exact resolve eq13 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2967 : ∀ X0 : G, (M.op x X0) ≠ X0 ∨ (M.op (M.op x y) X0) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq712 eq228
    | (have j0 := eq228 X0
       grind)
    | exact resolve eq228 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq2968 : ∀ X0 : G, (M.op x X0) ≠ X0 ∨ (k X0 (M.op (σ x) (σ y))) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq712 eq2967
    | (have j0 := eq2967 X0
       grind)
    | exact resolve eq2967 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2967
  have eq2977 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1653 eq2968
    | exact resolve eq2968 eq1653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2998 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X1) X2)) = (M.op x (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq712 eq208
    | exact resolve eq208 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq2999 : ∀ X2 X3 : G, (M.op X3 (M.op (M.op x y) X2)) = (M.op x (M.op X3 X2)) := by
    intro X2 X3
    first
    | (have i₁ := eq2998 x x X2 X3
       have i₂ := eq212 x x X2
       grind)
    | (have i₁ := eq2998 x y X2 X3
       have i₂ := eq212 x x X2
       grind)
    | exact superpose eq212 eq2998
    | (have j0 := eq2998 x y X2 X3
       grind)
    | exact resolve eq2998 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq2998
  have eq3000 : ∀ X2 X3 : G, (M.op x (M.op X3 X2)) = (M.op X3 (M.op x X2)) := by
    intro X2 X3
    first
    | exact superpose eq712 eq2999
    | exact resolve eq2999 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2999
  have eq6274 : (σ (σ (M.op x y))) ≠ (σ (σ (M.op x y))) ∨ (σ (σ (M.op x y))) = (M.op (σ (σ (M.op x y))) (σ (σ (M.op x y)))) := by
    first
    | exact superpose eq904 eq805
    | (have j0 := eq805 (σ (M.op x y))
       grind)
    | exact resolve eq805 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6279 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq805 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq805
    | (have j0 := eq805 (τ X0)
       grind)
    | exact resolve eq805 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6286 : (σ (σ (M.op x y))) = (M.op (σ (σ (M.op x y))) (σ (σ (M.op x y)))) := by grind
  clear eq6274
  have eq6294 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6279 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6279
    | (have j0 := eq6279 X0
       grind)
    | exact resolve eq6279 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6279
  have eq6302 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6294 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6294
    | (have j0 := eq6294 X0
       grind)
    | exact resolve eq6294 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6294
  have eq7083 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (σ (M.op x y)))) := by
    first
    | exact superpose eq6286 eq1725
    | exact resolve eq1725 eq6286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1725 eq6286
  have eq7140 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) (σ (M.op x y))) := by
    first
    | exact superpose eq7083 eq278
    | exact resolve eq278 eq7083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq7083
  have eq8027 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 (M.op x X1)) ∨ (M.op X0 (M.op (M.op x y) X1)) = (k (M.op X0 X1) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq712 eq528
    | (have j0 := eq528 X0 X1
       grind)
    | exact resolve eq528 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq8028 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 (M.op x X1)) ∨ (k (M.op X0 X1) (M.op x y)) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | exact superpose eq712 eq8027
    | (have j0 := eq8027 X0 X1
       grind)
    | exact resolve eq8027 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8027
  have eq8115 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op x (M.op X0 X1)) ∨ (k (M.op X0 X1) (M.op x y)) = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8028 x x
       have i₂ := eq3000 x x
       grind)
    | (have i₁ := eq8028 x x
       have i₂ := eq3000 x x
       grind)
    | exact superpose eq3000 eq8028
    | exact resolve eq8028 eq3000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3000 eq8028
  have eq8419 : ∀ X0 X1 : G, (M.op (σ X1) (σ (k X0 X1))) = (M.op x (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | exact superpose eq712 eq800
    | (have j0 := eq800 X0 X1
       grind)
    | exact resolve eq800 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712 eq800
  have eq8674 : ∀ X0 X1 : G, (M.op x (σ X0)) = (σ (k (k X0 X1) X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 (k X0 X1) X1
       have i₂ := eq8419 X0 X1
       grind)
    | exact superpose eq8419 eq88
    | (have j0 := eq88 X0 X1
       have j1 := eq8419 X0 X1
       grind)
    | exact resolve eq88 eq8419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq8419
  have eq8695 : ∀ X0 X1 : G, (M.op x (σ X0)) = (σ (k (k X0 X1) X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq8674 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8674
  have eq9089 : ∀ X0 : G, (σ x) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) X0) = X0 ∨ (M.op X0 X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq806 x X0
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq806
    | (have j0 := eq806 x X0
       grind)
    | exact resolve eq806 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq9091 : ∀ X0 : G, (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ (M.op X0 X0) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq132 eq806
    | (have j0 := eq806 (M.op x y) X0
       grind)
    | exact resolve eq806 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq806
  have eq9100 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ (M.op X0 X0) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq904 eq9091
    | (have j0 := eq9091 X0
       grind)
    | (have r₁ := eq9091 X0
       have r₂ := eq904
       grind)
    | exact resolve eq9091 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904 eq9091
  have eq9102 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = X0 ∨ (M.op X0 X0) = (k X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq728 eq9089
    | (have j0 := eq9089 X0
       grind)
    | (have r₁ := eq9089 X0
       have r₂ := eq728
       grind)
    | exact resolve eq9089 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728 eq9089
  have eq9111 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ (M.op X0 X0) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq9100 X0
       grind)
    | (have r₁ := eq9100 X0
       have r₂ := eq20
       grind)
    | exact resolve eq9100 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9100
  have eq9113 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (M.op X0 X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq9102 X0
       grind)
    | (have r₁ := eq9102 X0
       have r₂ := eq22
       grind)
    | exact resolve eq9102 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9102
  have eq9119 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ (M.op X0 X0) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq9111
    | (have j0 := eq9111 X0
       grind)
    | exact resolve eq9111 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9111
  have eq9121 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (M.op X0 X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq9113 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9113
    | (have j0 := eq9113 X0
       grind)
    | exact resolve eq9113 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9113
  have eq9127 : ∀ X0 : G, (M.op x X0) = X0 ∨ (M.op X0 X0) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1042 eq9119
    | (have j0 := eq9119 X0
       grind)
    | exact resolve eq9119 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042 eq9119
  have eq9128 : ∀ X0 : G, (M.op x X0) = X0 ∨ (M.op X0 X0) = (k X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq1512 eq9121
    | (have j0 := eq9121 X0
       grind)
    | exact resolve eq9121 eq1512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1512 eq9121
  have eq9130 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op x y))) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq9127
    | (have j0 := eq9127 X0
       grind)
    | exact resolve eq9127 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9127
  have eq9131 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9128 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9128
    | (have j0 := eq9128 X0
       grind)
    | exact resolve eq9128 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq9128
  have eq12571 : ∀ X0 : G, (k X0 (σ x)) = (k X0 (σ (M.op x y))) ∨ (M.op x X0) = X0 ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9130 X0
       have i₂ := eq9131 X0
       grind)
    | (have i₁ := eq9130 x
       have i₂ := eq9131 x
       grind)
    | exact superpose eq9131 eq9130
    | (have j0 := eq9130 X0
       have j1 := eq9131 X0
       grind)
    | exact resolve eq9130 eq9131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12647 : ∀ X0 : G, (k X0 (σ x)) = (k X0 (σ (M.op x y))) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12571 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12571
  have eq53392 : ∀ X0 : G, (M.op x (σ y)) = (σ (k (τ (k (σ y) X0)) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq8695 y (τ X0)
       have i₂ := eq301 X0
       grind)
    | exact superpose eq301 eq8695
    | (have j0 := eq8695 X0 (τ X0)
       grind)
    | exact resolve eq8695 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq53816 : ∀ X0 : G, (M.op x (σ y)) = (k (k (σ y) X0) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq53392 X0
       have i₂ := eq34 (k sF3 X0) (τ X0)
       grind)
    | exact superpose eq34 eq53392
    | (have j0 := eq53392 X0
       grind)
    | exact resolve eq53392 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53392
  have eq54143 : ∀ X0 : G, (M.op x (σ y)) = (k (k (σ y) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq53816 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq53816
    | (have j0 := eq53816 X0
       grind)
    | exact resolve eq53816 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53816
  have eq54342 : ∀ X0 : G, (M.op x (σ y)) = (k (k (σ y) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq54143 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq54143
    | (have j0 := eq54143 X0
       grind)
    | exact resolve eq54143 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54143
  have eq54426 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (k (σ y) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | exact superpose eq1653 eq54342
    | (have j0 := eq54342 X0
       grind)
    | exact resolve eq54342 eq1653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54342
  have eq54451 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (k (σ y) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq54426 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq54426
    | (have j0 := eq54426 X0
       grind)
    | exact resolve eq54426 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54426
  have eq66744 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op x y)) = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq8115 X0 X1
       have j1 := eq1291 X0 X1
       grind)
    | (have r₁ := eq8115 X0 X1
       have r₂ := eq1291 X0 X1
       grind)
    | exact resolve eq8115 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1291 eq8115
  have eq74345 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (k (M.op X0 X1) (M.op (σ x) (σ y))) ∨ (M.op X0 X1) = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq1653 eq1404
    | (have j0 := eq1404 X0 X1 x
       grind)
    | exact resolve eq1404 eq1653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1404
  have eq74469 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (k (M.op X0 X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have j0 := eq74345 X0 X1
       have j1 := eq2968 (M.op X0 X1)
       grind)
    | (have r₁ := eq74345 X0 X1
       have r₂ := eq2968 (M.op X0 X1)
       grind)
    | exact resolve eq74345 eq2968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2968 eq74345
  have eq90643 : (σ (k y y)) = (k (σ y) (M.op x y)) ∨ (σ y) = (k (σ y) (M.op x y)) ∨ (σ y) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq1278 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1278
    | (have j0 := eq1278 y
       grind)
    | exact resolve eq1278 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278
  have eq90790 : (k (σ y) (σ y)) = (k (σ y) (M.op x y)) ∨ (σ y) = (k (σ y) (M.op x y)) ∨ (σ y) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq90643
       have i₂ := eq81
       grind)
    | exact superpose eq81 eq90643
    | exact resolve eq90643 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq90643
  have eq90802 : (k (σ y) (σ y)) = (k (σ y) (M.op x y)) ∨ (σ y) = (M.op x (σ y)) := by
    first
    | (have j1 := eq1265 (σ y)
       grind)
    | (have r₁ := eq90790
       have r₂ := eq1265 (σ y)
       grind)
    | exact resolve eq90790 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265 eq90790
  have eq90810 : (k (σ y) (σ y)) = (k (σ y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1653 eq90802
    | exact resolve eq90802 eq1653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90802
  have eq90822 : (k y y) = (τ (k (σ y) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq90810 eq108
    | exact resolve eq108 eq90810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq90810
  have eq90852 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op x (σ y)) := by
    first
    | exact superpose eq1080 eq90822
    | (have j1 := eq1080 (σ y)
       grind)
    | exact resolve eq90822 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080 eq90822
  have eq90886 : (σ y) = (M.op (σ x) (σ y)) ∨ (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1653 eq90852
    | exact resolve eq90852 eq1653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90852
  have eq90887 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq90886
  have eq384853 : ∀ X0 X1 : G, (M.op x (σ (τ X0))) = (σ (k (τ (k X0 X1)) (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8695 (τ X0) (τ X1)
       have i₂ := eq472 X1 X0
       grind)
    | exact superpose eq472 eq8695
    | (have j0 := eq8695 X0 (τ X1)
       grind)
    | exact resolve eq8695 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472 eq8695
  have eq384864 : ∀ X0 X1 : G, (M.op x (σ (τ X0))) = (k (k X0 X1) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq384853 X0 X1
       have i₂ := eq34 (k X0 X1) (τ X1)
       grind)
    | exact superpose eq34 eq384853
    | (have j0 := eq384853 X0 X1
       grind)
    | exact resolve eq384853 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq384853
  have eq384997 : ∀ X0 X1 : G, (k (k X0 X1) X1) = (M.op x (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq384864 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq384864
    | (have j0 := eq384864 X0 X1
       grind)
    | exact resolve eq384864 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384864
  have eq385118 : ∀ X0 X1 : G, (M.op x X0) = (k (k X0 X1) X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq384997 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq384997
    | (have j0 := eq384997 X0 X1
       grind)
    | exact resolve eq384997 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384997
  have eq385203 : ∀ X0 X1 : G, (M.op x X0) = (k (k X0 X1) X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq385118 X0 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq385118
    | (have j0 := eq385118 X0 X1
       grind)
    | exact resolve eq385118 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385118
  have eq653611 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (k X0 (M.op (σ x) (σ y))) ∨ (M.op x X0) = X0 ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9130 X0
       have i₂ := eq1724 X0
       grind)
    | (have i₁ := eq9130 x
       have i₂ := eq1724 x
       grind)
    | exact superpose eq1724 eq9130
    | (have j0 := eq9130 X0
       have j1 := eq1724 X0
       grind)
    | exact resolve eq9130 eq1724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9130
  have eq653612 : ∀ X0 : G, (k X0 (σ x)) = (k X0 (M.op (σ x) (σ y))) ∨ (M.op x X0) = X0 ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9131 X0
       have i₂ := eq1724 X0
       grind)
    | (have i₁ := eq9131 x
       have i₂ := eq1724 x
       grind)
    | exact superpose eq1724 eq9131
    | (have j0 := eq9131 X0
       have j1 := eq1724 X0
       grind)
    | exact resolve eq9131 eq1724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1724 eq9131
  have eq654237 : ∀ X0 : G, (k X0 (σ x)) = (k X0 (M.op (σ x) (σ y))) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq653612 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653612
  have eq654238 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (k X0 (M.op (σ x) (σ y))) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq653611 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653611
  have eq759405 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1653 eq2470
    | exact resolve eq2470 eq1653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq869961 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (k (M.op X0 X1) (σ x)) ∨ (M.op X0 X1) = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq654237 eq74469
    | (have j1 := eq654237 (M.op X0 X1)
       grind)
    | exact resolve eq74469 eq654237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654237
  have eq870539 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (k (M.op X0 X1) (σ x)) := by
    intro X0 X1
    first
    | (have j0 := eq869961 X0 X1
       have j1 := eq1664 (M.op X0 X1)
       grind)
    | (have r₁ := eq869961 X0 X1
       have r₂ := eq1664 (M.op X0 X1)
       grind)
    | exact resolve eq869961 eq1664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1664 eq869961
  have eq871030 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (k (M.op X0 X1) (σ (M.op x y))) ∨ (M.op X0 X1) = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq870539 eq12647
    | (have j0 := eq12647 (M.op X0 X1)
       grind)
    | exact resolve eq12647 eq870539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12647 eq870539
  have eq871071 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (k (M.op X0 X1) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have j0 := eq871030 X0 X1
       have j1 := eq2470 (M.op X0 X1)
       grind)
    | (have r₁ := eq871030 X0 X1
       have r₂ := eq2470 (M.op X0 X1)
       grind)
    | exact resolve eq871030 eq2470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2470 eq871030
  have eq1592251 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq176
       have i₂ := eq385203 y y
       grind)
    | exact superpose eq385203 eq176
    | (have j1 := eq385203 x y
       grind)
    | exact resolve eq176 eq385203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq385203
  have eq1592457 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1592251
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1592251
    | exact resolve eq1592251 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1592251
  have eq1595008 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1592457
    | exact resolve eq1592457 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1592457
  have eq1596221 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1595008 eq54451
    | (have j0 := eq54451 (σ y)
       grind)
    | exact resolve eq54451 eq1595008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54451
  have eq1596281 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1596221
       have r₂ := eq27
       grind)
    | exact resolve eq1596221 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596221
  have eq1596310 : (τ (σ y)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1596281 eq90887
    | exact resolve eq90887 eq1596281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90887 eq1596281
  have eq1596471 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq1596310
    | exact resolve eq1596310 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596310
  have eq1596491 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq6302 y
       grind)
    | (have r₁ := eq1596471
       have r₂ := eq6302 y
       grind)
    | exact resolve eq1596471 eq6302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6302 eq1596471
  have eq1596516 : y ≠ y ∨ y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq1596491
       grind)
    | exact superpose eq1596491 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq1596491
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1596491
       grind)
    | exact resolve eq13 eq1596491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1596563 : (M.op x y) = (k y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq66744 y y
       have i₂ := eq1596491
       grind)
    | exact superpose eq1596491 eq66744
    | exact resolve eq66744 eq1596491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66744 eq1596491
  have eq1596607 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1596516
  have eq1596614 : (M.op x y) = (k y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1596563
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1596563
    | exact resolve eq1596563 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596563
  have eq1597005 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq805 y
       have i₂ := eq1596607
       grind)
    | exact superpose eq1596607 eq805
    | (have j0 := eq805 y
       grind)
    | exact resolve eq805 eq1596607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805 eq1596607
  have eq1597074 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1597005
  have eq1597135 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1597074
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1597074
    | exact resolve eq1597074 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1597074
  have eq1601701 : (M.op x (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1597135 eq74469
    | exact resolve eq74469 eq1597135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74469 eq1597135
  have eq1601791 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1653 eq1601701
    | exact resolve eq1601701 eq1653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601701
  have eq1601849 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq1601791
       have r₂ := eq2977
       grind)
    | exact resolve eq1601791 eq2977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2977 eq1601791
  have eq1603635 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op x (σ y)) := by
    first
    | exact superpose eq1601849 eq654238
    | (have j0 := eq654238 (σ y)
       grind)
    | exact resolve eq654238 eq1601849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654238 eq1601849
  have eq1603718 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1653 eq1603635
    | exact resolve eq1603635 eq1653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1653 eq1603635
  have eq1603737 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq1603718
       have r₂ := eq759405
       grind)
    | exact resolve eq1603718 eq759405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759405 eq1603718
  have eq1603757 : (k y (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1603737 eq114
    | exact resolve eq114 eq1603737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq1603737
  have eq1605467 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1596614 eq1603757
    | exact resolve eq1603757 eq1596614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596614 eq1603757
  have eq1606415 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1605467 eq15
    | exact resolve eq15 eq1605467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1605467
  have eq1606945 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1606415
    | exact resolve eq1606415 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1606415
  have eq1607021 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1606945
       have r₂ := eq27
       grind)
    | exact resolve eq1606945 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1606945
  have eq1607077 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq1607021 eq27
    | exact resolve eq27 eq1607021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq1607090 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq1607021 eq1726
    | exact resolve eq1726 eq1607021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726
  have eq1607117 : (τ (σ y)) = (k (τ (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1607021 eq7140
    | exact resolve eq7140 eq1607021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7140 eq1607021
  have eq1608476 : y = (k y (σ (M.op x y))) := by
    first
    | exact superpose eq29 eq1607117
    | exact resolve eq1607117 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1607117
  have eq1609751 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1607090 eq1595008
    | exact resolve eq1595008 eq1607090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1595008
  have eq1609879 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1607090 eq1609751
    | exact resolve eq1609751 eq1607090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1607090 eq1609751
  have eq1609914 : y = (M.op y y) := by
    first
    | (have r₁ := eq1609879
       have r₂ := eq1607077
       grind)
    | exact resolve eq1609879 eq1607077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1609879
  have eq1613221 : (M.op x y) = (k y (σ (M.op x y))) := by
    first
    | (have i₁ := eq871071 y y
       have i₂ := eq1609914
       grind)
    | exact superpose eq1609914 eq871071
    | exact resolve eq871071 eq1609914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871071 eq1609914
  have eq1613261 : y = (M.op x y) := by
    first
    | exact superpose eq1608476 eq1613221
    | exact resolve eq1613221 eq1608476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1608476 eq1613221
  have eq1613305 : y = (M.op x y) := by
    first
    | (have i₁ := eq1613261
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1613261
    | exact resolve eq1613261 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1613261
  have eq1613363 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1613305 eq20
    | exact resolve eq20 eq1613305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1613305
  have eq1614820 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1613363
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1613363
    | exact resolve eq1613363 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1613363
  have eq1614943 : False := by grind
  exact eq1614943

/-- `Equation443`: `x = x ◇ (y ◇ (y ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pyx_x_pyx_Equation443 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law443 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law443.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X1)))) = X0 := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq53 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 (M.op X1 X0)) X0
       have i₂ := eq14 (M.op X0 (M.op X1 X0)) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k (M.op X1 (M.op X1 (M.op X2 X1))) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 (M.op X1 (M.op X2 X1))) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have r₁ := eq13 (M.op X1 (M.op X1 (M.op X2 X1))) X0
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X1 (M.op X2 X1))) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq65 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq76 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq84 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq84
    | (have j0 := eq84 (σ X0) (σ X1)
       grind)
    | exact resolve eq84 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq84
    | (have j0 := eq84 (σ y) (σ X0)
       grind)
    | exact resolve eq84 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq76
       have i₂ := eq84 y x
       grind)
    | exact superpose eq84 eq76
    | (have j1 := eq84 y x
       grind)
    | exact resolve eq76 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
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
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq353 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (σ (M.op X1 (M.op X1 (M.op X2 X1)))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 X0 (M.op X1 (M.op X1 (M.op X2 X1)))
       have i₂ := eq66 (τ X0) X1 X2
       grind)
    | exact superpose eq66 eq38
    | exact resolve eq38 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq354 : ∀ X0 X1 X2 : G, (k (σ (M.op X1 (M.op X1 (M.op X2 X1)))) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq353 X0 X1 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq353
    | exact resolve eq353 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq626 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq96 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq644 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq116 eq84
    | (have j0 := eq84 (σ y) (σ x)
       grind)
    | exact resolve eq84 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq645 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq644
    | exact resolve eq644 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq648 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq645
       have r₂ := eq27
       grind)
    | exact resolve eq645 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq654 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ x) (σ x)))) = X0 ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq648 eq14
    | exact resolve eq14 eq648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq754 : ∀ X0 : G, x = (M.op y x) ∨ (k (σ x) X0) = X0 := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f754_12 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X1 (M.op X2 X1))) X0) = X0 := by
      intro X0 X1 X2
      grind
    have f754_13 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ x) (σ x)))) = X0 ∨ x = (M.op y x) := by
      intro X0
      grind
    have f754_21 : x ≠ (M.op y x) := by grind
    have f754_22 : X0 ≠ (k (σ x) X0) := by grind
    have f754_24 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ x) (σ x)))) = X0 := by
      intro X0
      first
      | (have j0 := f754_13 X0
         grind)
      | (have r₁ := f754_13 X0
         have r₂ := f754_21
         grind)
      | exact resolve f754_13 f754_21
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f754_93 : ∀ X0 : G, (k (σ x) X0) = X0 := by
      intro X0
      first
      | (have i₁ := f754_12 X0 (σ x) (σ x)
         have i₂ := f754_24 (σ x)
         grind)
      | exact superpose f754_24 f754_12
      | exact resolve f754_12 f754_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f754_110 : X0 ≠ X0 := by
      first
      | (have i₁ := f754_22
         have i₂ := f754_93 X0
         grind)
      | exact superpose f754_93 f754_22
      | (have r₁ := f754_22
         have r₂ := f754_93 X0
         grind)
      | exact resolve f754_22 f754_93
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f754_116 : False := by grind
    exact f754_116
  clear eq66 eq654
  have eq789 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op x x))) = X0 ∨ (k (σ x) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq754 X1
       grind)
    | exact superpose eq754 eq14
    | (have j1 := eq754 X1
       grind)
    | exact resolve eq14 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq3818 : ∀ X0 X1 : G, (k (σ x) X0) = X0 ∨ (k (σ x) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq354 X0 x x
       have i₂ := eq789 x X1
       grind)
    | exact superpose eq789 eq354
    | (have j1 := eq789 X0 X0
       grind)
    | exact resolve eq354 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq789
  have eq3845 : ∀ X0 X1 : G, (k (σ x) X1) = X1 ∨ (k (σ x) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3818 X1 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3818
    | (have j0 := eq3818 X1 X1
       grind)
    | exact resolve eq3818 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3818
  have eq3953 : ∀ X0 : G, X0 ≠ X0 ∨ (k (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3845 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3845
  have eq3954 : ∀ X0 : G, (k (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3953 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3953
  have eq3995 : (τ (σ x)) = (k x x) := by
    first
    | exact superpose eq3954 eq49
    | exact resolve eq49 eq3954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq3998 : x = (k x x) := by
    first
    | exact superpose eq28 eq3995
    | exact resolve eq3995 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3995
  have eq4026 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq84 x x
       have i₂ := eq3998
       grind)
    | exact superpose eq3998 eq84
    | (have j0 := eq84 x x
       grind)
    | exact resolve eq84 eq3998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq4027 : x = (M.op x x) := by grind
  clear eq4026
  have eq4060 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq626 x
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq626
    | (have j0 := eq626 x
       grind)
    | exact resolve eq626 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq4093 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3954 eq4060
    | (have r₁ := eq4060
       have r₂ := eq3954 (σ x)
       grind)
    | exact resolve eq4060 eq3954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4060
  have eq4102 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq4093
       have r₂ := eq22
       grind)
    | exact resolve eq4093 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4093
  have eq4105 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4102
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4102
    | exact resolve eq4102 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4102
  have eq4122 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) = X0 := by
    intro X0
    first
    | exact superpose eq4105 eq53
    | exact resolve eq53 eq4105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4132 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq4105 eq4122
    | exact resolve eq4122 eq4105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4122
  have eq4143 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq4105 eq4132
    | exact resolve eq4132 eq4105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4132
  have eq4238 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) (M.op x x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 x x x
       have i₂ := eq4027
       grind)
    | exact superpose eq4027 eq53
    | exact resolve eq53 eq4027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq4248 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq4238 X0
       have i₂ := eq4027
       grind)
    | exact superpose eq4027 eq4238
    | exact resolve eq4238 eq4027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4238
  have eq4255 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq4248 X0
       have i₂ := eq4027
       grind)
    | exact superpose eq4027 eq4248
    | exact resolve eq4248 eq4027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4248
  have eq4316 : (σ (k y (k x x))) = (M.op (k (σ x) (σ x)) (σ y)) ∨ (k (σ x) (σ x)) = (M.op (σ y) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq98 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq98
    | exact resolve eq98 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq98
  have eq4358 : (M.op (σ x) (σ y)) = (σ (k y (k x x))) ∨ (k (σ x) (σ x)) = (M.op (σ y) (k (σ x) (σ x))) := by
    first
    | exact superpose eq3954 eq4316
    | exact resolve eq4316 eq3954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4316
  have eq4385 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (k (σ x) (σ x)) = (M.op (σ y) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq4358
       have i₂ := eq3998
       grind)
    | exact superpose eq3998 eq4358
    | exact resolve eq4358 eq3998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3998 eq4358
  have eq4396 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (M.op (σ y) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq4385
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq4385
    | exact resolve eq4385 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq4385
  have eq4404 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (M.op (σ y) (k (σ x) (σ x))) := by
    first
    | exact superpose eq26 eq4396
    | exact resolve eq4396 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4396
  have eq4408 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq3954 eq4404
    | exact resolve eq4404 eq3954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3954 eq4404
  have eq4410 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq4143 eq4408
    | exact resolve eq4408 eq4143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4143 eq4408
  have eq4811 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq4410 eq116
    | exact resolve eq116 eq4410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq4410
  have eq4814 : x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq4811
       have r₂ := eq27
       grind)
    | exact resolve eq4811 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4811
  have eq4818 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4814
       have i₂ := eq4255 y
       grind)
    | exact superpose eq4255 eq4814
    | exact resolve eq4814 eq4255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4255 eq4814
  have eq4821 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq4818 eq29
    | exact resolve eq29 eq4818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4818
  have eq4860 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq4821
    | exact resolve eq4821 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4821
  have eq4861 : x = y := by grind
  clear eq4860
  have eq4877 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4861
       grind)
    | exact superpose eq4861 eq18
    | exact resolve eq18 eq4861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4878 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq4861
       grind)
    | exact superpose eq4861 eq24
    | exact resolve eq24 eq4861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4861
  have eq4929 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq4878
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4878
    | exact resolve eq4878 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4878
  have eq4930 : x = (M.op x y) := by
    first
    | (have i₁ := eq4877
       have i₂ := eq4027
       grind)
    | exact superpose eq4027 eq4877
    | exact resolve eq4877 eq4027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4027 eq4877
  have eq4940 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4929 eq26
    | exact resolve eq26 eq4929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4929
  have eq4979 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4105 eq4940
    | exact resolve eq4940 eq4105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4105 eq4940
  have eq5126 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq4930 eq20
    | exact resolve eq20 eq4930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4930
  have eq5178 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq5126
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5126
    | exact resolve eq5126 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5126
  have eq5213 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq4979 eq27
    | exact resolve eq27 eq4979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq4979
  have eq5255 : False := by grind
  exact eq5255

/-- `Equation443`: `x = x ◇ (y ◇ (y ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_y_pyx_Equation443 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law443 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law443.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
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
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq37
  have eq75 : x ≠ (M.op x y) ∨ y = (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq112
    | exact resolve eq112 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq113
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq113
    | exact resolve eq113 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq782 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq94 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq14768 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq114 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14769 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14768
    | exact resolve eq14768 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14768
  have eq14780 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14769
       have r₂ := eq28
       grind)
    | exact resolve eq14769 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14769
  have eq14782 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14780
    | exact resolve eq14780 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14780
  have eq14784 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq14782
  have eq14820 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14784
    | exact resolve eq14784 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14784
  have eq15680 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14820 eq114
    | exact resolve eq114 eq14820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14820
  have eq15692 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15680
  have eq15694 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq15692
       have r₂ := eq28
       grind)
    | exact resolve eq15692 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15692
  have eq15697 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15694
  have eq15733 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15697
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15697
    | exact resolve eq15697 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15697
  have eq16618 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq15733
       grind)
    | exact superpose eq15733 eq72
    | exact resolve eq72 eq15733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15733
  have eq16642 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq16618
    | exact resolve eq16618 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16618
  have eq16697 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16642 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq16642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16700 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq16697
    | exact resolve eq16697 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16697
  have eq16711 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq16700
       have r₂ := eq28
       grind)
    | exact resolve eq16700 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16700
  have eq16713 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq16711
    | exact resolve eq16711 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16711
  have eq16714 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16713
  have eq17025 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16714
  have eq17063 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq17025
    | exact resolve eq17025 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17025
  have eq17081 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17063 eq16642
    | exact resolve eq16642 eq17063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16642 eq17063
  have eq17088 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17081
  have eq17092 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17088
       have r₂ := eq28
       grind)
    | exact resolve eq17088 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17088
  have eq17281 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17092 eq28
    | exact resolve eq28 eq17092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17283 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17092 eq76
    | (have r₁ := eq76
       have r₂ := eq17092
       grind)
    | exact resolve eq76 eq17092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq17305 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq17283
  have eq18835 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq17305
  have eq18879 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq18835
    | exact resolve eq18835 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18835
  have eq20508 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq114 eq18879
    | exact resolve eq18879 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq20528 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq18879
  have eq20532 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq20508
  have eq20534 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20528
       have r₂ := eq17092
       grind)
    | exact resolve eq20528 eq17092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17092 eq20528
  have eq20536 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq20532
       have r₂ := eq17281
       grind)
    | exact resolve eq20532 eq17281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17281 eq20532
  have eq20538 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20536
       have r₂ := eq28
       grind)
    | exact resolve eq20536 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20536
  have eq20764 : (τ (σ x)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20534 eq83
    | exact resolve eq83 eq20534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq20534
  have eq20803 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq20764
    | exact resolve eq20764 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq20764
  have eq20810 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq20538
  have eq20866 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20810
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20810
    | exact resolve eq20810 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20810
  have eq21088 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20803
       have i₂ := eq20866
       grind)
    | exact superpose eq20866 eq20803
    | exact resolve eq20803 eq20866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20803 eq20866
  have eq21096 : x = (M.op x y) := by grind
  clear eq21088
  have eq21252 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq21096 eq21
    | exact resolve eq21 eq21096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq21258 : x ≠ x ∨ y = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq21096 eq75
    | (have r₁ := eq75
       have r₂ := eq21096
       grind)
    | exact resolve eq75 eq21096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq21326 : y = (M.op x x) ∨ x = (k y x) := by grind
  clear eq21258
  have eq21377 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq21252
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21252
    | exact resolve eq21252 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21252
  have eq21378 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq21377 eq27
    | exact resolve eq27 eq21377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22741 : (M.op x y) = (k y x) ∨ x = (k y x) := by grind
  clear eq21326
  have eq22797 : (M.op x y) = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq22741
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq22741
    | exact resolve eq22741 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq22741
  have eq22826 : x = (k y x) ∨ x = (k y x) := by
    first
    | exact superpose eq21096 eq22797
    | exact resolve eq22797 eq21096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21096 eq22797
  have eq22827 : x = (k y x) := by grind
  clear eq22826
  have eq22847 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq22827
       grind)
    | exact superpose eq22827 eq72
    | exact resolve eq72 eq22827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq22862 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq782 x y
       have i₂ := eq22827
       grind)
    | exact superpose eq22827 eq782
    | (have j0 := eq782 x y
       grind)
    | exact resolve eq782 eq22827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782 eq22827
  have eq22863 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq22862
  have eq22870 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq22863
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq22863
    | exact resolve eq22863 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22863
  have eq22883 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21377 eq22847
    | exact resolve eq22847 eq21377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22847
  have eq22885 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq22870
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22870
    | exact resolve eq22870 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22870
  have eq22897 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq22883
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22883
    | exact resolve eq22883 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22883
  have eq22898 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq22885
    | exact resolve eq22885 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq22885
  have eq22909 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21377 eq22897
    | exact resolve eq22897 eq21377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22897
  have eq22910 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21377 eq22898
    | exact resolve eq22898 eq21377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22898
  have eq22916 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq22910
       have r₂ := eq28
       grind)
    | exact resolve eq22910 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22910
  have eq22922 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq22916
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22916
    | exact resolve eq22916 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq22916
  have eq22928 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21377 eq22922
    | exact resolve eq22922 eq21377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21377 eq22922
  have eq22934 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq22928
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq22928
    | exact resolve eq22928 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq22928
  have eq23008 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq22934
  have eq23064 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21378 eq23008
    | exact resolve eq23008 eq21378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21378 eq23008
  have eq23072 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22909 eq23064
    | exact resolve eq23064 eq22909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22909 eq23064
  have eq23073 : False := by grind
  exact eq23073

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_y_pxx_y_pyx_Equation4430 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4430 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
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
  have eq55 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X2 X3 (M.op x X5) X5
       have i₂ := eq14 X0 X1 x X5
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq79 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq83 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq37 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq78
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq78
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq78 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq97
    | exact resolve eq97 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21 eq103
    | exact resolve eq103 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq105 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq79
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq79 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq79
       grind)
    | exact superpose eq79 eq16
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq105
  have eq213 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq56 X0 (M.op X0 x)
       have i₂ := eq56 X0 x
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq56 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56
    | (have j0 := eq56 x y
       grind)
    | exact resolve eq56 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq56 x x
       have i₂ := eq14 x x X0 X1
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq57 x x
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq57
    | exact resolve eq57 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq228 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op x y) y) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq225 eq14
    | exact resolve eq14 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) (σ y)) := by
    first
    | (have i₁ := eq228 x x
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq228
    | exact resolve eq228 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq347 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq216 eq213
    | exact resolve eq213 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq348 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq216 eq218
    | exact resolve eq218 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq351 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | exact superpose eq216 eq229
    | exact resolve eq229 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq416 : ∀ X0 : G, (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq347 eq13
    | (have j0 := eq13 X0 (M.op x (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (M.op x (M.op x y))
       have r₂ := eq347 X0
       grind)
    | exact resolve eq13 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq416 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq489 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op x y) y) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq55 x x X2 X3 X5
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq490 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X2 X3 X5
    first
    | exact superpose eq216 eq489
    | exact resolve eq489 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq491 : ∀ X5 : G, (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | (have i₁ := eq490 x x X5
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq490
    | exact resolve eq490 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq492 : ∀ X5 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | exact superpose eq216 eq491
    | exact resolve eq491 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq572 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (k X0 (M.op x (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq348 X0 X0
       have i₂ := eq423 X0
       grind)
    | exact superpose eq423 eq348
    | exact resolve eq348 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq423 eq35
    | exact resolve eq35 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq666 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq81 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq667 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq666 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq3789 : (σ (M.op x (M.op x y))) ≠ (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) ∨ (σ (M.op x (M.op x y))) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq423 eq667
    | (have j0 := eq667 (M.op x (M.op x y))
       grind)
    | exact resolve eq667 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq3804 : (σ (M.op x (M.op x y))) ≠ (σ (M.op x (M.op x y))) ∨ (σ (M.op x (M.op x y))) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq347 eq3789
    | exact resolve eq3789 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347 eq3789
  have eq3805 : (σ (M.op x (M.op x y))) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by grind
  clear eq3804
  have eq3812 : (σ (M.op x (M.op x y))) = (k (σ (M.op x (M.op x y))) (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq3805
       have i₂ := eq423 (σ (M.op x sF0))
       grind)
    | exact superpose eq423 eq3805
    | exact resolve eq3805 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3805
  have eq4518 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq83 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq83
    | (have j0 := eq83 y
       grind)
    | exact resolve eq83 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq4528 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq4518
  have eq4537 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4528
       have i₂ := eq79
       grind)
    | exact superpose eq79 eq4528
    | exact resolve eq4528 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq4528
  have eq4560 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq4537
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq4537 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4537
  have eq4589 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq4560 eq110
    | exact resolve eq110 eq4560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq13196 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq4560 eq111
    | exact resolve eq111 eq4560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq4560
  have eq17106 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq13196
       grind)
    | exact superpose eq13196 eq16
    | exact resolve eq16 eq13196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13196
  have eq17160 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq4589 eq17106
    | exact resolve eq17106 eq4589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17106
  have eq17165 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq17160
       have r₂ := eq13 y y
       grind)
    | exact resolve eq17160 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17160
  have eq21846 : (M.op x (M.op x y)) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq3812 eq572
    | exact resolve eq572 eq3812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21866 : (M.op x (M.op x y)) = (k (σ (M.op x (M.op x y))) (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq21846
       have i₂ := eq423 (σ (M.op x sF0))
       grind)
    | exact superpose eq423 eq21846
    | exact resolve eq21846 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423 eq21846
  have eq21872 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq3812 eq21866
    | exact resolve eq21866 eq3812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3812 eq21866
  have eq21878 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21872 eq575
    | exact resolve eq575 eq21872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq21881 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq21872 eq16
    | exact resolve eq16 eq21872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22390 : ∀ X0 : G, (k (σ X0) (M.op x (M.op x y))) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq21878 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq21878
    | exact resolve eq21878 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21878
  have eq23040 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq22390 eq572
    | exact resolve eq572 eq22390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq22390
  have eq29105 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq104 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq29106 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq29105
    | exact resolve eq29105 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29105
  have eq29121 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq29106
       have r₂ := eq28
       grind)
    | exact resolve eq29106 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29106
  have eq29129 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29121 eq4589
    | exact resolve eq4589 eq29121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4589 eq29121
  have eq29160 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq29129
       have i₂ := eq17165
       grind)
    | exact superpose eq17165 eq29129
    | exact resolve eq29129 eq17165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17165 eq29129
  have eq29173 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq29160
    | exact resolve eq29160 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29160
  have eq29174 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq29173
  have eq29185 : (M.op (M.op x y) y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29174 eq56
    | exact resolve eq56 eq29174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29189 : (M.op x (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq216 eq29185
    | exact resolve eq29185 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29185
  have eq31841 : (σ x) = (M.op x (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29189 eq29174
    | exact resolve eq29174 eq29189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29174 eq29189
  have eq31850 : (σ x) = (M.op x (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq31841
  have eq32066 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq31850 eq351
    | exact resolve eq351 eq31850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32083 : (σ x) = (τ (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq31850 eq21881
    | exact resolve eq21881 eq31850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21881 eq31850
  have eq32111 : x = (M.op y y) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq32083
    | exact resolve eq32083 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq32083
  have eq32115 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq32066
    | exact resolve eq32066 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32066
  have eq32132 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq23040 y
       have i₂ := eq32111
       grind)
    | exact superpose eq32111 eq23040
    | exact resolve eq23040 eq32111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32140 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq348 y y
       have i₂ := eq32111
       grind)
    | exact superpose eq32111 eq348
    | exact resolve eq348 eq32111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32111
  have eq32143 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq32140
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq32140
    | exact resolve eq32140 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32140
  have eq32149 : (M.op x (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq32132
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32132
    | exact resolve eq32132 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32132
  have eq32163 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq32149
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq32149
    | exact resolve eq32149 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32149
  have eq32168 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq32163
    | exact resolve eq32163 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32163
  have eq32181 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq23040 y
       have i₂ := eq32115
       grind)
    | exact superpose eq32115 eq23040
    | exact resolve eq23040 eq32115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23040
  have eq32189 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq348 y y
       have i₂ := eq32115
       grind)
    | exact superpose eq32115 eq348
    | exact resolve eq348 eq32115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348 eq32115
  have eq32192 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq32189
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq32189
    | exact resolve eq32189 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32189
  have eq32198 : (M.op x (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq32181
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32181
    | exact resolve eq32181 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq32181
  have eq32212 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq32198
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq32198
    | exact resolve eq32198 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32198
  have eq32217 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq32212
    | exact resolve eq32212 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32212
  have eq32306 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq32143 eq21872
    | exact resolve eq21872 eq32143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32338 : x = (M.op y x) ∨ x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq32306
    | exact resolve eq32306 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32306
  have eq32351 : (M.op (M.op x y) y) = (M.op y x) ∨ x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq32338
       grind)
    | exact superpose eq32338 eq56
    | exact resolve eq56 eq32338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32355 : (M.op y x) = (M.op x (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq216 eq32351
    | exact resolve eq32351 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32351
  have eq32691 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op y x) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq32168 eq32143
    | exact resolve eq32143 eq32168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32143 eq32168
  have eq32700 : x = (M.op y x) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq32691
  have eq32722 : (M.op (M.op x y) y) = (M.op y x) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq32700
       grind)
    | exact superpose eq32700 eq56
    | exact resolve eq56 eq32700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32726 : (M.op y x) = (M.op x (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq216 eq32722
    | exact resolve eq32722 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32722
  have eq33003 : (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq32192 eq21872
    | exact resolve eq21872 eq32192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33039 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq33003
    | exact resolve eq33003 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33003
  have eq33070 : (M.op (M.op x y) y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq33039
       grind)
    | exact superpose eq33039 eq56
    | exact resolve eq56 eq33039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33074 : (M.op y x) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq216 eq33070
    | exact resolve eq33070 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33070
  have eq33291 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq32217 eq32192
    | exact resolve eq32192 eq32217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32192 eq32217
  have eq33301 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq33291
  have eq33324 : (M.op (M.op x y) y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq33301
       grind)
    | exact superpose eq33301 eq56
    | exact resolve eq56 eq33301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq33328 : (M.op y x) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq216 eq33324
    | exact resolve eq33324 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33324
  have eq36442 : x = (M.op x (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq32338
       have i₂ := eq32355
       grind)
    | exact superpose eq32355 eq32338
    | exact resolve eq32338 eq32355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32338 eq32355
  have eq36463 : x = (M.op x (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq36442
  have eq36928 : x = (σ x) ∨ x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq36463 eq21872
    | exact resolve eq21872 eq36463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36463
  have eq36974 : x = (σ x) ∨ x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq36928
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq36928
    | exact resolve eq36928 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36928
  have eq36975 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by grind
  clear eq36974
  have eq87351 : x = (M.op x (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32700
       have i₂ := eq32726
       grind)
    | exact superpose eq32726 eq32700
    | exact resolve eq32700 eq32726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32700 eq32726
  have eq87372 : x = (M.op x (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq87351
  have eq87419 : x = (σ x) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq87372 eq21872
    | exact resolve eq21872 eq87372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21872 eq87372
  have eq87472 : x = (σ x) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq87419
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq87419
    | exact resolve eq87419 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87419
  have eq87473 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by grind
  clear eq87472
  have eq87480 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq87473 eq28
    | exact resolve eq28 eq87473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87473
  have eq87491 : x = (σ x) := by
    first
    | (have r₁ := eq87480
       have r₂ := eq36975
       grind)
    | exact resolve eq87480 eq36975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36975 eq87480
  have eq87493 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq87491 eq27
    | exact resolve eq27 eq87491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq106671 : (M.op y x) = (M.op x (M.op x y)) ∨ x = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq87491 eq33074
    | exact resolve eq33074 eq87491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33074
  have eq106681 : (M.op y x) = (M.op x (M.op x y)) ∨ x = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq87491 eq33328
    | exact resolve eq33328 eq87491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33328
  have eq108823 : x = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq33039
       have i₂ := eq106671
       grind)
    | exact superpose eq106671 eq33039
    | exact resolve eq33039 eq106671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33039 eq106671
  have eq108838 : x = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) := by grind
  clear eq108823
  have eq108852 : x = (M.op (σ x) (σ y)) ∨ x = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq87491 eq108838
    | exact resolve eq108838 eq87491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108838
  have eq108853 : x = (M.op x (M.op x y)) ∨ x = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq108852
  have eq108882 : x = (M.op x (σ y)) ∨ x = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq108853 eq351
    | exact resolve eq351 eq108853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108853
  have eq108954 : x = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq87493 eq108882
    | exact resolve eq108882 eq87493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108882
  have eq108955 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) := by grind
  clear eq108954
  have eq198005 : x = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33301
       have i₂ := eq106681
       grind)
    | exact superpose eq106681 eq33301
    | exact resolve eq33301 eq106681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33301 eq106681
  have eq198023 : x = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) := by grind
  clear eq198005
  have eq198034 : x = (M.op (σ x) (σ y)) ∨ x = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq87491 eq198023
    | exact resolve eq198023 eq87491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198023
  have eq198035 : x = (M.op x (M.op x y)) ∨ x = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq198034
  have eq199252 : x = (M.op x (σ y)) ∨ x = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq198035 eq351
    | exact resolve eq351 eq198035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351 eq198035
  have eq199331 : x = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq87493 eq199252
    | exact resolve eq199252 eq87493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199252
  have eq199332 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) := by grind
  clear eq199331
  have eq199347 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq199332 eq28
    | exact resolve eq28 eq199332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199332
  have eq199361 : x = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq199347
       have r₂ := eq108955
       grind)
    | exact resolve eq199347 eq108955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108955 eq199347
  have eq199364 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq199361 eq28
    | exact resolve eq28 eq199361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq199366 : (M.op (M.op x y) y) = (M.op x (σ y)) := by
    first
    | exact superpose eq199361 eq225
    | exact resolve eq225 eq199361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq199376 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq87493 eq199366
    | exact resolve eq199366 eq87493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87493 eq199366
  have eq199378 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq216 eq199376
    | exact resolve eq199376 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq199376
  have eq199379 : x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq199361 eq199378
    | exact resolve eq199378 eq199361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199361 eq199378
  have eq200570 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq199379 eq492
    | exact resolve eq492 eq199379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492 eq199379
  have eq200810 : x = (M.op x y) := by
    first
    | (have i₁ := eq200570 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq200570
    | (have j0 := eq200570 y
       grind)
    | exact resolve eq200570 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq200570
  have eq201517 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq200810 eq21
    | exact resolve eq21 eq200810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq200810
  have eq202061 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq201517
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq201517
    | exact resolve eq201517 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq201517
  have eq202203 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq87491 eq202061
    | exact resolve eq202061 eq87491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87491 eq202061
  have eq202284 : False := by grind
  exact eq202284

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pxx_y_pyx_Equation4430 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4430 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
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
  have eq55 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X2 X3 (M.op x X5) X5
       have i₂ := eq14 X0 X1 x X5
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq79 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq83 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq37 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq78
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq78 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq95
    | exact resolve eq95 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq101
    | exact resolve eq101 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq102
    | exact resolve eq102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq109 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq79
       grind)
    | exact superpose eq79 eq16
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq213 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq56 X0 (M.op X0 x)
       have i₂ := eq56 X0 x
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq56 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56
    | (have j0 := eq56 x y
       grind)
    | exact resolve eq56 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq56 x x
       have i₂ := eq14 x x X0 X1
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq57 x x
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq57
    | exact resolve eq57 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq228 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op x y) y) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq225 eq14
    | exact resolve eq14 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) (σ y)) := by
    first
    | (have i₁ := eq228 x x
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq228
    | exact resolve eq228 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq347 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq216 eq213
    | exact resolve eq213 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq348 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq216 eq218
    | exact resolve eq218 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq351 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | exact superpose eq216 eq229
    | exact resolve eq229 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq489 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op x y) y) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq55 x x X2 X3 X5
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq490 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X2 X3 X5
    first
    | exact superpose eq216 eq489
    | exact resolve eq489 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq491 : ∀ X5 : G, (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | (have i₁ := eq490 x x X5
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq490
    | exact resolve eq490 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq492 : ∀ X5 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | exact superpose eq216 eq491
    | exact resolve eq491 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq655 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq81 X0 X1
       grind)
    | exact superpose eq81 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq81 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq81 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq81 X0 X1
       grind)
    | exact resolve eq13 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq678 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq655 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq655 X1 X1
       have r₂ := eq13 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq655 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq655 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq688 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq678 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq678
    | (have j0 := eq678 X0 X1
       grind)
    | exact resolve eq678 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq4313 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq83 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq83
    | (have j0 := eq83 y
       grind)
    | exact resolve eq83 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq4324 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq4313
  have eq4333 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4324
       have i₂ := eq79
       grind)
    | exact superpose eq79 eq4324
    | exact resolve eq4324 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq4324
  have eq4357 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq4333
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq4333 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4333
  have eq4385 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq4357 eq109
    | exact resolve eq109 eq4357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq4357
  have eq7218 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq688 X0 (M.op X0 X0)
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq688
    | (have j0 := eq688 X0 (M.op X0 X0)
       grind)
    | exact resolve eq688 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq688
  have eq7335 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq7218 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7218
  have eq7336 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq7335 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7335
  have eq7877 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7336 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq7336
    | exact resolve eq7336 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7959 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq7336 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq7336
    | (have j0 := eq7336 y
       grind)
    | exact resolve eq7336 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7972 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq348 (σ X0) (σ X0)
       have i₂ := eq7336 X0
       grind)
    | exact superpose eq7336 eq348
    | exact resolve eq348 eq7336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8239 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq7959
       grind)
    | exact superpose eq7959 eq16
    | exact resolve eq16 eq7959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7959
  have eq8267 : (M.op y y) = (k y y) := by
    first
    | exact superpose eq4385 eq8239
    | exact resolve eq8239 eq4385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8239
  have eq9253 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq7877 X0
       grind)
    | exact superpose eq7877 eq16
    | exact resolve eq16 eq7877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7877
  have eq9485 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq56 (τ X0) (τ X0)
       have i₂ := eq9253 X0
       grind)
    | exact superpose eq9253 eq56
    | exact resolve eq56 eq9253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq9491 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq216 eq9485
    | exact resolve eq9485 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9485
  have eq10986 : (M.op x (M.op x y)) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq492 eq7972
    | exact resolve eq7972 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11197 : (M.op x (M.op x y)) = (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq10986
       have i₂ := eq7336 (M.op x sF0)
       grind)
    | exact superpose eq7336 eq10986
    | exact resolve eq10986 eq7336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7336 eq10986
  have eq11281 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq492 eq11197
    | exact resolve eq11197 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11197
  have eq11329 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq11281 eq16
    | exact resolve eq16 eq11281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16773 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq16774 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq16773
    | exact resolve eq16773 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16773
  have eq16787 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq16774
       have r₂ := eq28
       grind)
    | exact resolve eq16774 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16774
  have eq16792 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq16787
    | exact resolve eq16787 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16787
  have eq16794 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16792 eq4385
    | exact resolve eq4385 eq16792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4385 eq16792
  have eq16815 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16794
       have i₂ := eq8267
       grind)
    | exact superpose eq8267 eq16794
    | exact resolve eq16794 eq8267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8267 eq16794
  have eq16821 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq16815
    | exact resolve eq16815 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16815
  have eq16822 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16821
  have eq16827 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7972 y
       have i₂ := eq16822
       grind)
    | exact superpose eq16822 eq7972
    | exact resolve eq7972 eq16822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7972
  have eq16836 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq348 y y
       have i₂ := eq16822
       grind)
    | exact superpose eq16822 eq348
    | exact resolve eq348 eq16822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348 eq16822
  have eq16838 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16836
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16836
    | exact resolve eq16836 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16836
  have eq16845 : (M.op x (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16827
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16827
    | exact resolve eq16827 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq16827
  have eq16851 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16845
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16845
    | exact resolve eq16845 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16845
  have eq16853 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq16851
    | exact resolve eq16851 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16851
  have eq16937 : (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16838 eq11281
    | exact resolve eq11281 eq16838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11281
  have eq16951 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq16937
    | exact resolve eq16937 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16937
  have eq16957 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16951 eq225
    | exact resolve eq225 eq16951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16960 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq216 eq16957
    | exact resolve eq16957 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16957
  have eq16961 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq16960
    | exact resolve eq16960 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16960
  have eq17058 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16853 eq16838
    | exact resolve eq16838 eq16853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16838 eq16853
  have eq17067 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17058
  have eq17264 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17067 eq225
    | exact resolve eq225 eq17067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq17266 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  have eq17268 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq216 eq17264
    | exact resolve eq17264 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17264
  have eq17269 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq17268
    | exact resolve eq17268 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17268
  have eq18590 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16961 eq492
    | exact resolve eq492 eq16961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18604 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16961 eq11329
    | exact resolve eq11329 eq16961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16961
  have eq18695 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16951 eq18604
    | exact resolve eq18604 eq16951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18604
  have eq18729 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq18695
  have eq18732 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq18729
    | exact resolve eq18729 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18729
  have eq18904 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17269 eq347
    | exact resolve eq347 eq17269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq18906 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17269 eq492
    | exact resolve eq492 eq17269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq18920 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17269 eq11329
    | exact resolve eq11329 eq17269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11329 eq17269
  have eq19011 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17067 eq18920
    | exact resolve eq18920 eq17067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18920
  have eq19047 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq19011
  have eq19050 : (σ x) = (τ (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq19047
       have r₂ := eq17266
       grind)
    | exact resolve eq19047 eq17266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19047
  have eq19051 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq29 eq19050
    | exact resolve eq19050 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq19050
  have eq19054 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq19051 eq28
    | exact resolve eq28 eq19051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19051
  have eq19076 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19054
       have r₂ := eq18732
       grind)
    | exact resolve eq19054 eq18732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18732 eq19054
  have eq19512 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16951 eq18590
    | exact resolve eq18590 eq16951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16951 eq18590
  have eq19541 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq19512 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19512
  have eq19562 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17067 eq18904
    | exact resolve eq18904 eq17067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17067 eq18904
  have eq19601 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq19562 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19562
  have eq19618 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq19601 X0
       grind)
    | (have r₁ := eq19601 X0
       have r₂ := eq17266
       grind)
    | exact resolve eq19601 eq17266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17266 eq19601
  have eq19789 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19076 eq19541
    | exact resolve eq19541 eq19076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19541
  have eq19838 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq19789 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19789
  have eq19898 : ∀ X0 : G, x = (M.op X0 x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19076 eq19618
    | exact resolve eq19618 eq19076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19076 eq19618
  have eq19948 : ∀ X0 : G, x = (M.op X0 x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq19898 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19898
  have eq22877 : x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq19838 y
       grind)
    | exact superpose eq19838 eq19
    | (have j1 := eq19838 y
       grind)
    | exact resolve eq19 eq19838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19838
  have eq22944 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq22877
  have eq24153 : x = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18906 x
       have i₂ := eq19948 sF4
       grind)
    | exact superpose eq19948 eq18906
    | exact resolve eq18906 eq19948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19948
  have eq24158 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24153
  have eq24194 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24158 eq28
    | exact resolve eq28 eq24158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24158
  have eq24226 : x = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq24194
       have r₂ := eq22944
       grind)
    | exact resolve eq24194 eq22944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22944 eq24194
  have eq24454 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq24226 eq18906
    | exact resolve eq18906 eq24226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18906 eq24226
  have eq24467 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq24454 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24454
  have eq24515 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq24467 y
       grind)
    | exact superpose eq24467 eq19
    | (have j1 := eq24467 y
       grind)
    | exact resolve eq19 eq24467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24467
  have eq24582 : x = (M.op x y) := by grind
  clear eq24515
  have eq24825 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq24582 eq21
    | exact resolve eq21 eq24582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq24870 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq24582 eq216
    | exact resolve eq216 eq24582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq24878 : (M.op x x) = (M.op (M.op x x) (σ y)) := by
    first
    | exact superpose eq24582 eq351
    | exact resolve eq351 eq24582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq24926 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq24870
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24870
    | exact resolve eq24870 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq24870
  have eq24970 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq24825
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq24825
    | exact resolve eq24825 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24825
  have eq24971 : x = (M.op x x) := by
    first
    | exact superpose eq24582 eq24926
    | exact resolve eq24926 eq24582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24926
  have eq25017 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq24970 eq27
    | exact resolve eq27 eq24970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq25224 : (M.op x (M.op x y)) = (M.op (τ x) (τ x)) := by
    first
    | (have i₁ := eq9491 x
       have i₂ := eq24971
       grind)
    | exact superpose eq24971 eq9491
    | exact resolve eq9491 eq24971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9491
  have eq25237 : (M.op x (M.op x y)) = (τ (M.op x x)) := by
    first
    | (have i₁ := eq25224
       have i₂ := eq9253 x
       grind)
    | exact superpose eq9253 eq25224
    | exact resolve eq25224 eq9253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9253 eq25224
  have eq25247 : (M.op x (M.op x y)) = (τ x) := by
    first
    | (have i₁ := eq25237
       have i₂ := eq24971
       grind)
    | exact superpose eq24971 eq25237
    | exact resolve eq25237 eq24971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25237
  have eq25256 : (M.op x x) = (τ x) := by
    first
    | exact superpose eq24582 eq25247
    | exact resolve eq25247 eq24582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24582 eq25247
  have eq25262 : x = (τ x) := by
    first
    | (have i₁ := eq25256
       have i₂ := eq24971
       grind)
    | exact superpose eq24971 eq25256
    | exact resolve eq25256 eq24971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25256
  have eq25268 : x = (σ x) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq25262
       grind)
    | exact superpose eq25262 eq15
    | exact resolve eq15 eq25262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25262
  have eq25348 : x = (σ x) := by
    first
    | (have i₁ := eq25268
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq25268
    | exact resolve eq25268 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq25268
  have eq25366 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq24970 eq25348
    | exact resolve eq25348 eq24970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24970 eq25348
  have eq25716 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq25366 eq25017
    | exact resolve eq25017 eq25366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25017
  have eq27175 : x = (M.op x (σ y)) := by
    first
    | (have i₁ := eq24878
       have i₂ := eq24971
       grind)
    | exact superpose eq24971 eq24878
    | exact resolve eq24878 eq24971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24878 eq24971
  have eq27176 : x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25716 eq27175
    | exact resolve eq27175 eq25716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25716 eq27175
  have eq27181 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq27176 eq28
    | exact resolve eq28 eq27176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq27176
  have eq27218 : False := by grind
  exact eq27218

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pxx_pyx_pxy_Equation4430 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4430 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
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
  clear eq36
  have eq55 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X2 X3 (M.op x X5) X5
       have i₂ := eq14 X0 X1 x X5
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq37 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq37
    | exact resolve eq37 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq88
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq88
    | exact resolve eq88 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq21 eq96
    | exact resolve eq96 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq110 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq79
       grind)
    | exact superpose eq79 eq16
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq56 X0 (M.op X0 x)
       have i₂ := eq56 X0 x
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq56 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56
    | (have j0 := eq56 x y
       grind)
    | exact resolve eq56 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq56 x x
       have i₂ := eq14 x x X0 X1
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq11 (τ X0) X1
       grind)
    | exact superpose eq11 eq35
    | (have j1 := eq11 (τ X0) X1
       grind)
    | exact resolve eq35 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq306 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k y (τ X0))
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq361 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq377 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq215 eq212
    | exact resolve eq212 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq378 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq215 eq217
    | exact resolve eq217 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq400 : ∀ X0 : G, (M.op x (M.op x y)) ≠ X0 ∨ (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) = (k (M.op x (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq377 eq13
    | (have j0 := eq13 (M.op x (M.op x y)) X0
       grind)
    | (have r₁ := eq13 (M.op x (M.op x y)) (M.op x (M.op x y))
       have r₂ := eq377 (M.op x (M.op x y))
       grind)
    | exact resolve eq13 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq409 : ∀ X0 : G, (M.op x (M.op x y)) ≠ X0 ∨ (M.op x (M.op x y)) = (k (M.op x (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq377 eq400
    | (have j0 := eq400 X0
       grind)
    | (have r₁ := eq400 (M.op X0 (M.op x (M.op x y)))
       have r₂ := eq377 X0
       grind)
    | exact resolve eq400 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq527 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op x y) y) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq55 x x X2 X3 X5
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq528 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X2 X3 X5
    first
    | exact superpose eq215 eq527
    | exact resolve eq527 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq529 : ∀ X5 : G, (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | (have i₁ := eq528 x x X5
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq528
    | exact resolve eq528 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq528
  have eq530 : ∀ X5 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | exact superpose eq215 eq529
    | exact resolve eq529 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq529
  have eq539 : ∀ X0 : G, (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq530 eq13
    | (have j0 := eq13 X0 (M.op x (M.op x y))
       grind)
    | (have r₁ := eq13 x (M.op x (M.op x y))
       have r₂ := eq530 x
       grind)
    | exact resolve eq13 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq549 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq539 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq567 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (k X0 (M.op x (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq378 X0 X0
       have i₂ := eq549 X0
       grind)
    | exact superpose eq549 eq378
    | exact resolve eq378 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq570 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq549 eq35
    | exact resolve eq35 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq728 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq81 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq729 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq728 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq759 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq260 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq260
    | exact resolve eq260 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq822 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq549 eq361
    | exact resolve eq361 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq3371 : (σ (M.op x (M.op x y))) ≠ (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) ∨ (σ (M.op x (M.op x y))) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq549 eq729
    | (have j0 := eq729 (M.op x (M.op x y))
       grind)
    | exact resolve eq729 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq3386 : (σ (M.op x (M.op x y))) ≠ (σ (M.op x (M.op x y))) ∨ (σ (M.op x (M.op x y))) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq377 eq3371
    | exact resolve eq3371 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3371
  have eq3387 : (σ (M.op x (M.op x y))) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by grind
  clear eq3386
  have eq3394 : (σ (M.op x (M.op x y))) = (k (σ (M.op x (M.op x y))) (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq3387
       have i₂ := eq549 (σ (M.op x sF0))
       grind)
    | exact superpose eq549 eq3387
    | exact resolve eq3387 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3387
  have eq4028 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq195 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq195
    | (have j0 := eq195 y
       grind)
    | exact resolve eq195 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq4038 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq4028
  have eq4047 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4038
       have i₂ := eq79
       grind)
    | exact superpose eq79 eq4038
    | exact resolve eq4038 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq4038
  have eq4071 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq4047
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq4047 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4047
  have eq4094 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq4071 eq110
    | exact resolve eq110 eq4071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq4071
  have eq4704 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq257 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq257
    | exact resolve eq257 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq4792 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4704 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq4704
    | (have j0 := eq4704 X0 X1
       grind)
    | exact resolve eq4704 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4704
  have eq16272 : ∀ X0 : G, (k (τ X0) (τ (M.op x (M.op x y)))) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq822 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq822
    | exact resolve eq822 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq16532 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (k X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq16272 x
       have i₂ := eq759 (M.op x sF0) x
       grind)
    | exact superpose eq759 eq16272
    | exact resolve eq16272 eq759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759 eq16272
  have eq16763 : (M.op x (M.op x y)) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq3394 eq567
    | exact resolve eq567 eq3394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16783 : (M.op x (M.op x y)) = (k (σ (M.op x (M.op x y))) (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq16763
       have i₂ := eq549 (σ (M.op x sF0))
       grind)
    | exact superpose eq549 eq16763
    | exact resolve eq16763 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16763
  have eq16789 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq3394 eq16783
    | exact resolve eq16783 eq3394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3394 eq16783
  have eq16797 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq16789 eq570
    | exact resolve eq570 eq16789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq16800 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq16789 eq16
    | exact resolve eq16 eq16789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16805 : (σ (k (M.op x (M.op x y)) y)) = (k (M.op x (M.op x y)) (σ y)) := by
    first
    | exact superpose eq16789 eq41
    | exact resolve eq41 eq16789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq16896 : (k y (M.op x (M.op x y))) = (τ (k (σ y) (M.op x (M.op x y)))) := by
    first
    | exact superpose eq16800 eq306
    | exact resolve eq306 eq16800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq16931 : (τ (M.op (σ y) (σ y))) = (k y (M.op x (M.op x y))) := by
    first
    | exact superpose eq16532 eq16896
    | exact resolve eq16896 eq16532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16532 eq16896
  have eq16945 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq549 eq16931
    | exact resolve eq16931 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549 eq16931
  have eq16953 : (M.op y y) = (k y y) := by
    first
    | exact superpose eq4094 eq16945
    | exact resolve eq16945 eq4094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16945
  have eq17432 : ∀ X0 : G, (k (σ X0) (M.op x (M.op x y))) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16797 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq16797
    | exact resolve eq16797 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16797
  have eq17739 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq17432 eq567
    | exact resolve eq567 eq17432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567 eq17432
  have eq30406 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq30407 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27 eq30406
    | exact resolve eq30406 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30406
  have eq30422 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq30407
       have r₂ := eq28
       grind)
    | exact resolve eq30407 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30407
  have eq30433 : (M.op x (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30422 eq378
    | exact resolve eq378 eq30422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30442 : (σ y) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30433 eq30422
    | exact resolve eq30422 eq30433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30422 eq30433
  have eq30451 : (σ y) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq30442
  have eq30893 : (σ y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30451 eq16800
    | exact resolve eq16800 eq30451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16800
  have eq30932 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (σ y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30 eq30893
    | exact resolve eq30893 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq30893
  have eq30944 : (τ (σ x)) = (k y y) ∨ y = (σ y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30932 eq4094
    | exact resolve eq4094 eq30932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30932
  have eq30980 : (τ (σ x)) = (M.op y y) ∨ y = (σ y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq30944
       have i₂ := eq16953
       grind)
    | exact superpose eq16953 eq30944
    | exact resolve eq30944 eq16953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30944
  have eq30992 : x = (M.op y y) ∨ y = (σ y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq30980
    | exact resolve eq30980 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30980
  have eq30993 : y = (M.op y x) ∨ y = (σ y) ∨ x = (M.op y y) := by grind
  clear eq30992
  have eq31004 : (M.op y x) = (M.op x (M.op x y)) ∨ y = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq378 y x
       have i₂ := eq30993
       grind)
    | exact superpose eq30993 eq378
    | exact resolve eq378 eq30993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31414 : y = (M.op x (M.op x y)) ∨ y = (σ y) ∨ x = (M.op y y) ∨ y = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq30993
       have i₂ := eq31004
       grind)
    | exact superpose eq31004 eq30993
    | exact resolve eq30993 eq31004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30993 eq31004
  have eq31423 : y = (M.op x (M.op x y)) ∨ y = (σ y) ∨ x = (M.op y y) := by grind
  clear eq31414
  have eq31452 : y = (σ y) ∨ y = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31423 eq16789
    | exact resolve eq16789 eq31423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31423
  have eq31499 : y = (σ y) ∨ y = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq31452
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq31452
    | exact resolve eq31452 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31452
  have eq31500 : x = (M.op y y) ∨ y = (σ y) := by grind
  clear eq31499
  have eq31521 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq17739 y
       have i₂ := eq31500
       grind)
    | exact superpose eq31500 eq17739
    | exact resolve eq17739 eq31500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17739
  have eq31529 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq378 y y
       have i₂ := eq31500
       grind)
    | exact superpose eq31500 eq378
    | exact resolve eq378 eq31500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31500
  have eq31531 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq31529
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq31529
    | exact resolve eq31529 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31529
  have eq31537 : (M.op x (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq31521
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq31521
    | exact resolve eq31521 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31521
  have eq31551 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq31537
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq31537
    | exact resolve eq31537 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31537
  have eq31556 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq27 eq31551
    | exact resolve eq31551 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31551
  have eq31580 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq31531 eq16789
    | exact resolve eq16789 eq31531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31628 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq21 eq31580
    | exact resolve eq31580 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31580
  have eq32315 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq31556 eq31531
    | exact resolve eq31531 eq31556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31531 eq31556
  have eq32324 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq32315
  have eq32751 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq32324 eq28
    | exact resolve eq28 eq32324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32324
  have eq32752 : y = (σ y) := by
    first
    | (have r₁ := eq32751
       have r₂ := eq31628
       grind)
    | exact resolve eq32751 eq31628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31628 eq32751
  have eq32753 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq32752 eq27
    | exact resolve eq27 eq32752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq32811 : (k y y) = (τ (M.op y y)) := by
    first
    | exact superpose eq32752 eq4094
    | exact resolve eq4094 eq32752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4094
  have eq32837 : (M.op y y) = (τ (M.op y y)) := by
    first
    | (have i₁ := eq32811
       have i₂ := eq16953
       grind)
    | exact superpose eq16953 eq32811
    | exact resolve eq32811 eq16953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32811
  have eq274617 : (k (M.op x (M.op x y)) (σ y)) = (σ (M.op (M.op x (M.op x y)) y)) ∨ (M.op y y) = (M.op x (M.op x y)) ∨ y = (M.op y (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq16805
       have i₂ := eq4792 (M.op x sF0) y
       grind)
    | exact superpose eq4792 eq16805
    | (have j1 := eq4792 (M.op x (M.op x y)) y
       grind)
    | exact resolve eq16805 eq4792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4792 eq16805
  have eq275540 : (σ (M.op x (M.op x y))) = (k (M.op x (M.op x y)) (σ y)) ∨ (M.op y y) = (M.op x (M.op x y)) ∨ y = (M.op y (M.op x (M.op x y))) := by
    first
    | exact superpose eq530 eq274617
    | exact resolve eq274617 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq274617
  have eq275975 : (σ (M.op x (M.op x y))) = (k (M.op x (M.op x y)) y) ∨ (M.op y y) = (M.op x (M.op x y)) ∨ y = (M.op y (M.op x (M.op x y))) := by
    first
    | exact superpose eq32752 eq275540
    | exact resolve eq275540 eq32752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275540
  have eq276101 : (M.op x (M.op x y)) = (k (M.op x (M.op x y)) y) ∨ (M.op y y) = (M.op x (M.op x y)) ∨ y = (M.op y (M.op x (M.op x y))) := by
    first
    | exact superpose eq16789 eq275975
    | exact resolve eq275975 eq16789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275975
  have eq276174 : y = (M.op x (M.op x y)) ∨ (M.op x (M.op x y)) = (k (M.op x (M.op x y)) y) ∨ (M.op y y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq377 eq276101
    | exact resolve eq276101 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276101
  have eq276220 : (M.op x (M.op x y)) = (k (M.op x (M.op x y)) y) ∨ (M.op y y) = (M.op x (M.op x y)) := by
    first
    | (have j1 := eq409 y
       grind)
    | (have r₁ := eq276174
       have r₂ := eq409 y
       grind)
    | (have r₁ := eq276174
       have r₂ := eq409 (k (M.op x (M.op x y)) y)
       grind)
    | (have r₁ := eq276174
       have r₂ := eq409 (M.op y y)
       grind)
    | exact resolve eq276174 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409 eq276174
  have eq276268 : (σ y) = (k (σ y) y) ∨ (σ y) = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30451 eq276220
    | exact resolve eq276220 eq30451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30451 eq276220
  have eq276304 : y = (k y y) ∨ (σ y) = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32752 eq276268
    | exact resolve eq276268 eq32752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276268
  have eq276316 : y = (M.op y y) ∨ (σ y) = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq276304
       have i₂ := eq16953
       grind)
    | exact superpose eq16953 eq276304
    | exact resolve eq276304 eq16953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16953 eq276304
  have eq276321 : y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32752 eq276316
    | exact resolve eq276316 eq32752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276316
  have eq276322 : y = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq276321
  have eq276323 : (σ x) = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32752 eq276322
    | exact resolve eq276322 eq32752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276322
  have eq1438599 : (σ x) = (τ (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq32837
       have i₂ := eq276323
       grind)
    | exact superpose eq276323 eq32837
    | exact resolve eq32837 eq276323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1438841 : x ≠ (σ x) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq276323
  have eq1438980 : x = (σ x) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq1438599
    | exact resolve eq1438599 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1438599
  have eq1439108 : y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq1438980
       have r₂ := eq1438841
       grind)
    | exact resolve eq1438980 eq1438841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438841 eq1438980
  have eq1439362 : (M.op y y) = (M.op x (M.op x y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq378 y y
       have i₂ := eq1439108
       grind)
    | exact superpose eq1439108 eq378
    | exact resolve eq378 eq1439108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1439364 : x ≠ y ∨ x = (M.op y y) ∨ y = (M.op y x) := by grind
  have eq1439702 : y = (M.op x (M.op x y)) ∨ x = y ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1439362
       have i₂ := eq1439108
       grind)
    | exact superpose eq1439108 eq1439362
    | exact resolve eq1439362 eq1439108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439108 eq1439362
  have eq1439970 : y = (M.op x (M.op x y)) ∨ x = y ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq1439702
  have eq1440110 : y = (M.op y x) ∨ y = (M.op x (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1439970
       have r₂ := eq1439364
       grind)
    | exact resolve eq1439970 eq1439364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439364 eq1439970
  have eq1440330 : (M.op y x) = (M.op x (M.op x y)) ∨ y = (M.op x (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq378 y x
       have i₂ := eq1440110
       grind)
    | exact superpose eq1440110 eq378
    | exact resolve eq378 eq1440110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1440399 : y = (M.op x (M.op x y)) ∨ y = (M.op x (M.op x y)) ∨ x = (M.op y y) ∨ y = (M.op x (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1440110
       have i₂ := eq1440330
       grind)
    | exact superpose eq1440330 eq1440110
    | exact resolve eq1440110 eq1440330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440110 eq1440330
  have eq1440410 : y = (M.op x (M.op x y)) ∨ x = (M.op y y) := by grind
  clear eq1440399
  have eq1440446 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1440410 eq377
    | exact resolve eq377 eq1440410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377 eq1440410
  have eq1440913 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1440446 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1440446
    | (have j0 := eq1440446 x
       grind)
    | exact resolve eq1440446 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1440917 : x = (M.op y y) ∨ y = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32753 eq1440446
    | exact resolve eq1440446 eq32753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440446
  have eq1441648 : x = (τ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq32837
       have i₂ := eq1440913
       grind)
    | exact superpose eq1440913 eq32837
    | exact resolve eq32837 eq1440913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1441885 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq378 y y
       have i₂ := eq1440913
       grind)
    | exact superpose eq1440913 eq378
    | exact resolve eq378 eq1440913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq1440913
  have eq1441893 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1441885
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1441885
    | exact resolve eq1441885 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1441885
  have eq1442190 : x = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq1441648
       grind)
    | exact superpose eq1441648 eq15
    | exact resolve eq15 eq1441648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1441648
  have eq1442713 : y = (M.op x y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq1442190
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1442190
    | exact resolve eq1442190 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1442190
  have eq1442720 : (σ y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq1442713 eq21
    | exact resolve eq21 eq1442713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1442713
  have eq1444452 : (σ (M.op x y)) = (σ y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq1442720
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1442720
    | exact resolve eq1442720 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1442720
  have eq1444770 : y = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq32752 eq1444452
    | exact resolve eq1444452 eq32752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32752 eq1444452
  have eq1447511 : x = (τ x) ∨ y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32837
       have i₂ := eq1440917
       grind)
    | exact superpose eq1440917 eq32837
    | exact resolve eq32837 eq1440917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32837 eq1440917
  have eq1448053 : x = (σ x) ∨ y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq1447511
       grind)
    | exact superpose eq1447511 eq15
    | exact resolve eq15 eq1447511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447511
  have eq1448576 : y = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq1448053
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1448053
    | exact resolve eq1448053 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1448053
  have eq1448584 : y ≠ (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq1448576 eq28
    | exact resolve eq28 eq1448576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448576
  have eq1448597 : x = (σ x) := by
    first
    | (have r₁ := eq1448584
       have r₂ := eq1444770
       grind)
    | exact resolve eq1448584 eq1444770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1444770 eq1448584
  have eq1448713 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1448597 eq32753
    | exact resolve eq32753 eq1448597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32753 eq1448597
  have eq1449210 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1448713
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1448713
    | exact resolve eq1448713 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448713
  have eq1449311 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq1449210 eq28
    | exact resolve eq28 eq1449210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1449210
  have eq1450077 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1441893 eq16789
    | exact resolve eq16789 eq1441893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1441893
  have eq1450512 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq1450077
    | exact resolve eq1450077 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1450077
  have eq1450562 : y = (M.op x y) := by
    first
    | (have r₁ := eq1450512
       have r₂ := eq1449311
       grind)
    | exact resolve eq1450512 eq1449311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1450512
  have eq1450814 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1450562 eq16789
    | exact resolve eq16789 eq1450562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16789 eq1450562
  have eq1452248 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq1450814
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1450814
    | exact resolve eq1450814 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1450814
  have eq1453038 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq1452248
    | exact resolve eq1452248 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1452248
  have eq1453531 : False := by grind
  exact eq1453531

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxx_pyy_pxy_Equation4430 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law4430 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
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
  have eq50 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq14 X2 (M.op X2 x) X4 X5
       have i₂ := eq14 X2 x X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X4 X5 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X4 X5) X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq14 x x X4 X5
       have i₂ := eq14 x x X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X2 X3 (M.op x X5) X5
       have i₂ := eq14 X0 X1 x X5
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
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
  clear eq44
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq91
    | exact resolve eq91 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq214 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq55 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55
    | (have j0 := eq55 x y
       grind)
    | exact resolve eq55 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : (M.op (M.op x y) y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq55
    | (have j0 := eq55 (σ x) (σ y)
       grind)
    | exact resolve eq55 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq229 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq214 eq228
    | exact resolve eq228 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq232 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq229 eq14
    | exact resolve eq14 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq232 x x
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq232
    | exact resolve eq232 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq235 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | exact superpose eq214 eq233
    | exact resolve eq233 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq236 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq214 eq215
    | exact resolve eq215 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq259 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq16
    | exact resolve eq16 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq391 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq411 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq229 eq391
    | exact resolve eq391 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229 eq391
  have eq488 : ∀ X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op x (M.op x y))) := by
    intro X2 X4 X5
    first
    | (have i₁ := eq50 x x X2 X4 X5
       have i₂ := eq411 x x
       grind)
    | exact superpose eq411 eq50
    | exact resolve eq50 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq489 : ∀ X2 : G, (M.op x (M.op x y)) = (M.op X2 (M.op x (M.op x y))) := by
    intro X2
    first
    | (have i₁ := eq488 X2 x x
       have i₂ := eq411 x x
       grind)
    | exact superpose eq411 eq488
    | exact resolve eq488 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq502 : ∀ X0 : G, (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq489 eq13
    | (have j0 := eq13 X0 (M.op x (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (M.op x (M.op x y))
       have r₂ := eq489 (M.op x (M.op x y))
       grind)
    | exact resolve eq13 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq502 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq515 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op x y) y) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq54 x x X2 X3 X5
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq516 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X2 X3 X5
    first
    | exact superpose eq214 eq515
    | exact resolve eq515 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq517 : ∀ X5 : G, (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | (have i₁ := eq516 x x X5
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq516
    | exact resolve eq516 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq518 : ∀ X5 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | exact superpose eq214 eq517
    | exact resolve eq517 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq556 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (k X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq55 X0 X0
       have i₂ := eq506 X0
       grind)
    | exact superpose eq506 eq55
    | exact resolve eq55 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (k X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq214 eq556
    | exact resolve eq556 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq674 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq76 X0 X0
       grind)
    | exact superpose eq76 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq76 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq76 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq13 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq679 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq674 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq682 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq679 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq679 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq679 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq3358 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq506 eq682
    | (have j0 := eq682 (M.op x (M.op x y)) X0
       grind)
    | exact resolve eq682 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq3373 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op x (M.op x y))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq489 eq3358
    | (have j0 := eq3358 X0
       grind)
    | exact resolve eq3358 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3358
  have eq3374 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have j0 := eq3373 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3373
  have eq3404 : ∀ X0 : G, (k (τ X0) (M.op x (M.op x y))) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq3374 eq259
    | exact resolve eq259 eq3374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq3410 : (M.op (σ y) (σ y)) = (σ (k y (M.op x (M.op x y)))) := by
    first
    | exact superpose eq3374 eq36
    | exact resolve eq36 eq3374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq3374
  have eq3433 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq506 eq3410
    | exact resolve eq3410 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3410
  have eq3458 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq3433
       grind)
    | exact superpose eq3433 eq16
    | exact resolve eq16 eq3433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3615 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq506 eq3404
    | exact resolve eq3404 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq3620 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq3404 eq561
    | exact resolve eq561 eq3404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561 eq3404
  have eq3693 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3615 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq3615
    | exact resolve eq3615 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3829 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 (M.op (σ X0) (σ X0))
       have i₂ := eq3693 X0
       grind)
    | exact superpose eq3693 eq15
    | exact resolve eq15 eq3693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3693
  have eq4108 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq55 (σ X0) (σ X0)
       have i₂ := eq3829 X0
       grind)
    | exact superpose eq3829 eq55
    | exact resolve eq55 eq3829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4114 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq214 eq4108
    | exact resolve eq4108 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4108
  have eq4586 : (M.op x (M.op x y)) = (M.op (τ (M.op x (M.op x y))) (τ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq518 eq3620
    | exact resolve eq3620 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3620
  have eq4617 : (M.op x (M.op x y)) = (τ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq4586
       have i₂ := eq3615 (M.op x sF0)
       grind)
    | exact superpose eq3615 eq4586
    | exact resolve eq4586 eq3615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3615 eq4586
  have eq4636 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq518 eq4617
    | exact resolve eq4617 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518 eq4617
  have eq4650 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq4636 eq15
    | exact resolve eq15 eq4636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30082 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq92 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq30083 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq30082
    | exact resolve eq30082 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30082
  have eq30095 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq30083
       have r₂ := eq27
       grind)
    | exact resolve eq30083 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30083
  have eq30100 : (τ (σ y)) = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq30095 eq3458
    | exact resolve eq3458 eq30095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30095
  have eq30141 : y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq30100
    | exact resolve eq30100 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30100
  have eq30142 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq30141
  have eq30157 : (M.op x (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30142 eq411
    | exact resolve eq411 eq30142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30166 : (σ y) = (M.op x (M.op x y)) ∨ y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30157 eq30142
    | exact resolve eq30142 eq30157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30142 eq30157
  have eq30175 : (σ y) = (M.op x (M.op x y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq30166
  have eq30521 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30175 eq235
    | exact resolve eq235 eq30175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235 eq30175
  have eq62858 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30521 eq3458
    | exact resolve eq3458 eq30521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3458 eq30521
  have eq62899 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq62858
    | exact resolve eq62858 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62858
  have eq62900 : y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq62899
  have eq62910 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq3433
       have i₂ := eq62900
       grind)
    | exact superpose eq62900 eq3433
    | exact resolve eq3433 eq62900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62923 : (M.op x (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq4114 y
       have i₂ := eq62900
       grind)
    | exact superpose eq62900 eq4114
    | exact resolve eq4114 eq62900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4114
  have eq62930 : (M.op y y) = (M.op x (M.op x y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq411 y y
       have i₂ := eq62900
       grind)
    | exact superpose eq62900 eq411
    | exact resolve eq411 eq62900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62939 : (M.op x (M.op x y)) = (σ (M.op y y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq62923
       have i₂ := eq3829 y
       grind)
    | exact superpose eq3829 eq62923
    | exact resolve eq62923 eq3829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3829 eq62923
  have eq62951 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq62910
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq62910
    | exact resolve eq62910 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62910
  have eq62955 : (M.op x (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq62939
       have i₂ := eq3433
       grind)
    | exact superpose eq3433 eq62939
    | exact resolve eq62939 eq3433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3433 eq62939
  have eq63398 : y = (M.op x (M.op x y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq62900
       have i₂ := eq62930
       grind)
    | exact superpose eq62930 eq62900
    | exact resolve eq62900 eq62930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62900 eq62930
  have eq63414 : y = (M.op y x) ∨ y = (M.op x (M.op x y)) := by grind
  clear eq63398
  have eq64227 : (σ y) = (M.op x (M.op x y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq62955 eq62951
    | exact resolve eq62951 eq62955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62951 eq62955
  have eq64243 : (σ y) = (M.op x (M.op x y)) ∨ y = (M.op y x) := by grind
  clear eq64227
  have eq64285 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq64243 eq489
    | exact resolve eq489 eq64243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64302 : (σ y) = (τ (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq64243 eq4636
    | exact resolve eq4636 eq64243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4636 eq64243
  have eq64352 : y = (M.op y x) ∨ y = (σ y) := by
    first
    | exact superpose eq29 eq64302
    | exact resolve eq64302 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq64302
  have eq64736 : (M.op y x) = (M.op x (M.op x y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq411 y x
       have i₂ := eq64352
       grind)
    | exact superpose eq64352 eq411
    | exact resolve eq411 eq64352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64352
  have eq65142 : y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq64285
    | (have j0 := eq64285 (σ x)
       grind)
    | exact resolve eq64285 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64285
  have eq65233 : (M.op y x) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq411 y x
       have i₂ := eq65142
       grind)
    | exact superpose eq65142 eq411
    | exact resolve eq411 eq65142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411 eq65142
  have eq66121 : y = (M.op x (M.op x y)) ∨ y = (M.op x (M.op x y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq63414
       have i₂ := eq64736
       grind)
    | exact superpose eq64736 eq63414
    | exact resolve eq63414 eq64736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64736
  have eq66131 : y = (M.op x (M.op x y)) ∨ y = (σ y) := by grind
  clear eq66121
  have eq66166 : y = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq66131 eq4650
    | exact resolve eq4650 eq66131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4650 eq66131
  have eq66216 : y = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq66166
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq66166
    | exact resolve eq66166 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66166
  have eq66217 : y = (σ y) := by grind
  clear eq66216
  have eq66224 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq66217 eq26
    | exact resolve eq26 eq66217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq72851 : (M.op y x) = (M.op x (M.op x y)) ∨ y = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq66217 eq65233
    | exact resolve eq65233 eq66217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65233
  have eq73408 : y = (M.op x (M.op x y)) ∨ y = (M.op x (M.op x y)) ∨ y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq63414
       have i₂ := eq72851
       grind)
    | exact superpose eq72851 eq63414
    | exact resolve eq63414 eq72851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63414 eq72851
  have eq73420 : y = (M.op x (M.op x y)) ∨ y = (M.op (σ x) (σ y)) := by grind
  clear eq73408
  have eq73444 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq73420 eq489
    | exact resolve eq489 eq73420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489 eq73420
  have eq74158 : y = (M.op (σ x) (σ y)) ∨ y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq66224
       have i₂ := eq73444 sF2
       grind)
    | exact superpose eq73444 eq66224
    | exact resolve eq66224 eq73444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73444
  have eq74161 : y = (M.op (σ x) (σ y)) := by grind
  clear eq74158
  have eq74223 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq74161 eq27
    | exact resolve eq27 eq74161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq74227 : (M.op x (M.op x y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq74161 eq236
    | exact resolve eq236 eq74161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq74229 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq66224 eq74227
    | exact resolve eq74227 eq66224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66224 eq74227
  have eq74232 : y = (M.op x (M.op x y)) := by
    first
    | exact superpose eq74161 eq74229
    | exact resolve eq74229 eq74161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74161 eq74229
  have eq74837 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq74232 eq55
    | exact resolve eq55 eq74232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq74841 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq214 eq74837
    | exact resolve eq74837 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq74837
  have eq74864 : y = (M.op x y) := by
    first
    | exact superpose eq74232 eq74841
    | exact resolve eq74841 eq74232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74232 eq74841
  have eq74874 : y = (M.op x y) := by
    first
    | (have i₁ := eq74864
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq74864
    | exact resolve eq74864 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq74864
  have eq74880 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq74874 eq20
    | exact resolve eq20 eq74874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq74874
  have eq75219 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq74880
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq74880
    | exact resolve eq74880 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq74880
  have eq75380 : y = (σ (M.op x y)) := by
    first
    | exact superpose eq66217 eq75219
    | exact resolve eq75219 eq66217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66217 eq75219
  have eq75460 : False := by grind
  exact eq75460

/-- `Equation4452`: `x ◇ (y ◇ x) = (z ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxx_pyx_pxy_Equation4452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) X0) := by
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq176 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X3 X1) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X1 x X3
       have i₂ := eq16 X1 x X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X2 (M.op x X0)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y X0 x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) X0 (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
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
  have eq183 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X2 X0) ∨ (M.op X0 X0) = (k X0 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X2 X0)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 X0 (M.op X2 X0)
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : x ≠ (M.op x y) ∨ (k y x) = (M.op y y) := by
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
  have eq187 : (M.op (M.op x y) y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq179 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq179
    | (have j0 := eq179 x
       grind)
    | exact resolve eq179 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq180
    | (have j0 := eq180 (σ x)
       grind)
    | exact resolve eq180 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq854 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X1 X0) = (M.op X1 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 (M.op X1 X0) X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq11 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq856 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (k X0 X1) X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq863 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (k X0 (M.op X1 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq11 X0 (M.op X1 X0)
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 (M.op (M.op X2 X0) X0) (k X0 (M.op X1 X0))
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq874 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (k (M.op X0 X1) X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq11 (M.op X0 X1) X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 (M.op X0 X1) X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq882 : (M.op x y) = (k x y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq884 : (k y (M.op x y)) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq187
       have i₂ := eq11 y sF0
       grind)
    | exact superpose eq11 eq187
    | (have j1 := eq11 y (M.op x y)
       grind)
    | exact resolve eq187 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq888 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq905 : (k y (M.op x y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have j1 := eq12 y (M.op x y)
       grind)
    | (have r₁ := eq884
       have r₂ := eq12 (k y (M.op x y)) (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq884
       have r₂ := eq12 (M.op (M.op x y) y) (k y (M.op x y))
       grind)
    | (have r₁ := eq884
       have r₂ := eq12 y (M.op x y)
       grind)
    | exact resolve eq884 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884
  have eq942 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq943 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq942 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq942 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq942 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq944 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op X0 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq943 X0
       grind)
    | exact superpose eq943 eq16
    | exact resolve eq16 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq947 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X1 X0 X0
       have i₂ := eq943 X0
       grind)
    | exact superpose eq943 eq176
    | exact resolve eq176 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq949 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq181 X0 X1 X0
       have i₂ := eq943 X0
       grind)
    | exact superpose eq943 eq181
    | exact resolve eq181 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq951 : (M.op (M.op x y) y) = (M.op y (k y y)) := by
    first
    | (have i₁ := eq179 y
       have i₂ := eq943 y
       grind)
    | exact superpose eq943 eq179
    | exact resolve eq179 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq1022 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq944 X0 X0
       have i₂ := eq943 X0
       grind)
    | exact superpose eq943 eq944
    | exact resolve eq944 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1454 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (k X0 X0) X0) ∨ (k X0 X0) = X0 ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0) X0
       have i₂ := eq1022 X0
       grind)
    | exact superpose eq1022 eq11
    | (have j0 := eq11 (k X0 X0) X0
       grind)
    | exact resolve eq11 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1483 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (k X0 X0) X0) ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq1454 X0
       have j1 := eq12 (k X0 X0) X0
       grind)
    | (have r₁ := eq1454 X0
       have r₂ := eq12 (M.op X0 (k X0 X0)) (k (k X0 X0) X0)
       grind)
    | (have r₁ := eq1454 X0
       have r₂ := eq12 (k (k X0 X0) X0) (M.op X0 (k X0 X0))
       grind)
    | (have r₁ := eq1454 x
       have r₂ := eq12 (k x x) x
       grind)
    | exact resolve eq1454 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1454
  have eq1986 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X0 (M.op X2 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X0 (M.op X2 X0))
       have i₂ := eq178 X0 X2 X1
       grind)
    | exact superpose eq178 eq13
    | (have j0 := eq13 X0 (M.op X0 (M.op X2 X0))
       grind)
    | (have r₁ := eq13 X0 (M.op X0 (M.op X2 X0))
       have r₂ := eq178 X0 X2 X2
       grind)
    | exact resolve eq13 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2019 : ∀ X0 X2 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X2 X0))) := by
    intro X0 X2
    first
    | (have j0 := eq1986 X0 x X2
       grind)
    | (have r₁ := eq1986 X0 x X2
       have r₂ := eq181 X0 x X2
       grind)
    | (have r₁ := eq1986 X0 X2 x
       have r₂ := eq181 X0 x X2
       grind)
    | exact resolve eq1986 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq1986
  have eq2083 : ∀ X0 X2 : G, (k X0 X0) = (k X0 (M.op X0 (M.op X2 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq2019 X0 X2
       have i₂ := eq943 X0
       grind)
    | exact superpose eq943 eq2019
    | exact resolve eq2019 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2019
  have eq2153 : ∀ X0 X1 : G, (k X1 X1) = (k X1 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2083 X1 x
       have i₂ := eq16 X1 x X0
       grind)
    | exact superpose eq16 eq2083
    | exact resolve eq2083 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2268 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq882
       grind)
    | exact superpose eq882 eq40
    | exact resolve eq40 eq882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882
  have eq2269 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2268
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2268
    | exact resolve eq2268 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2268
  have eq2271 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq2269
    | exact resolve eq2269 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269
  have eq2963 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq2271 eq888
    | exact resolve eq888 eq2271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2970 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq2963
       have r₂ := eq27
       grind)
    | exact resolve eq2963 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2963
  have eq2975 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq2970 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq2970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2987 : (M.op (σ y) (σ x)) = (M.op (k (σ x) (σ x)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq2970 eq947
    | exact resolve eq947 eq2970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq2988 : (M.op (σ x) (σ y)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq2970 eq949
    | exact resolve eq949 eq2970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2990 : (k (σ x) (σ x)) = (k (σ x) (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq2970 eq2153
    | exact resolve eq2153 eq2970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2992 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op y x) := by grind
  clear eq2975
  have eq2994 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq2970 eq2990
    | exact resolve eq2990 eq2970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2990
  have eq2996 : (M.op (σ x) (σ y)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq2988
    | exact resolve eq2988 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2988
  have eq2997 : (M.op (σ y) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2987
       have i₂ := eq1022 sF2
       grind)
    | exact superpose eq1022 eq2987
    | exact resolve eq2987 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2987
  have eq3009 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq2992
    | exact resolve eq2992 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2992
  have eq3011 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq2271 eq2994
    | exact resolve eq2994 eq2271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2271 eq2994
  have eq3012 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq2996 eq2997
    | exact resolve eq2997 eq2996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2996 eq2997
  have eq3023 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2970 eq3012
    | exact resolve eq3012 eq2970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2970 eq3012
  have eq3314 : (τ (σ (M.op x y))) = (k x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq3011 eq97
    | exact resolve eq97 eq3011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq3011
  have eq3323 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq28 eq3314
    | exact resolve eq3314 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3314
  have eq3381 : (M.op x (M.op x y)) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1022 x
       have i₂ := eq3323
       grind)
    | exact superpose eq3323 eq1022
    | exact resolve eq1022 eq3323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5156 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq3009 eq141
    | exact resolve eq141 eq3009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq3009
  have eq5157 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq31 eq5156
    | exact resolve eq5156 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5156
  have eq5160 : y = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq3023 eq5157
    | exact resolve eq5157 eq3023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3023 eq5157
  have eq5161 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by grind
  clear eq5160
  have eq5793 : ∀ X0 : G, (M.op y x) = (M.op x (M.op X0 x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq856 y x X0
       have i₂ := eq5161
       grind)
    | exact superpose eq5161 eq856
    | (have j0 := eq856 x y x
       grind)
    | exact resolve eq856 eq5161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5911 : ∀ X0 : G, (M.op y x) = (M.op x (M.op X0 x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq5793 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5793
  have eq5964 : (M.op y x) = (M.op x (k x x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq5911 x
       have i₂ := eq949 x x
       grind)
    | exact superpose eq949 eq5911
    | exact resolve eq5911 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5911
  have eq6011 : x = (M.op x y) ∨ (M.op y x) = (M.op x (k x x)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq5964
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5964
    | exact resolve eq5964 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5964
  have eq6027 : x = (M.op x y) ∨ (M.op y x) = (M.op x (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq3323 eq6011
    | exact resolve eq6011 eq3323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6011
  have eq6035 : (M.op y x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq3381 eq6027
    | exact resolve eq6027 eq3381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3381 eq6027
  have eq6628 : (k y x) = (M.op (M.op x y) x) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq6035
       grind)
    | exact superpose eq6035 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq6035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6649 : y ≠ (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq6035
  have eq6650 : (k y x) = (M.op (M.op x y) x) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq6628
  have eq6656 : x = (M.op x y) ∨ (k y x) = (M.op (M.op x y) x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq6650
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6650
    | exact resolve eq6650 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6650
  have eq6657 : x = (M.op x y) ∨ (k y x) = (M.op (M.op x y) x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq6656
  have eq6661 : x = (M.op x y) ∨ y = (M.op (M.op x y) x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq5161 eq6657
    | exact resolve eq6657 eq5161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6657
  have eq6662 : y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq6661
       have r₂ := eq6649
       grind)
    | exact resolve eq6661 eq6649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6649 eq6661
  have eq6667 : y = (k y x) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq6662
       grind)
    | exact superpose eq6662 eq11
    | (have j0 := eq11 y (k y x)
       grind)
    | exact resolve eq11 eq6662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6676 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op (M.op x y) x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq178 x y X0
       have i₂ := eq6662
       grind)
    | exact superpose eq6662 eq178
    | exact resolve eq178 eq6662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq6683 : (M.op y x) = (M.op x (k x x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq944 x y
       have i₂ := eq6662
       grind)
    | exact superpose eq6662 eq944
    | exact resolve eq944 eq6662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq6685 : (M.op x y) = (M.op x (k x x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq949 x y
       have i₂ := eq6662
       grind)
    | exact superpose eq6662 eq949
    | exact resolve eq949 eq6662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6686 : (k x x) = (k x (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2083 x y
       have i₂ := eq6662
       grind)
    | exact superpose eq6662 eq2083
    | exact resolve eq2083 eq6662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6687 : (k x x) = (k x (M.op y x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2153 y x
       have i₂ := eq6662
       grind)
    | exact superpose eq6662 eq2153
    | exact resolve eq2153 eq6662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2153
  have eq6689 : y = (k y x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq6667
  have eq6694 : (k x x) = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6662 eq6687
    | exact resolve eq6687 eq6662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6687
  have eq6695 : (k x x) = (k x (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6686
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6686
    | exact resolve eq6686 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6686
  have eq6696 : (M.op x y) = (M.op x (k x x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6685
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6685
    | exact resolve eq6685 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6685
  have eq6698 : y = (M.op x (k x x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6662 eq6683
    | exact resolve eq6683 eq6662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6683
  have eq6705 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op (M.op x y) x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq6676 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6676
    | (have j0 := eq6676 X0
       grind)
    | exact resolve eq6676 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6676
  have eq6714 : x = (M.op x y) ∨ y = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6689
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6689
    | exact resolve eq6689 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6689
  have eq6715 : y = (k y x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq6714
  have eq6718 : (M.op x y) = (M.op x (k x (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6695 eq6696
    | exact resolve eq6696 eq6695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6696
  have eq6720 : y = (M.op x (k x (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6695 eq6698
    | exact resolve eq6698 eq6695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6698
  have eq6726 : (M.op x (k x x)) = (M.op (M.op x y) x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6705 x
       have i₂ := eq949 x x
       grind)
    | exact superpose eq949 eq6705
    | exact resolve eq6705 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6705
  have eq6734 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6718 eq6720
    | exact resolve eq6720 eq6718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6720
  have eq6740 : (M.op (M.op x y) x) = (M.op x (k x (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6695 eq6726
    | exact resolve eq6726 eq6695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6726
  have eq6750 : (M.op x y) = (M.op (M.op x y) x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6718 eq6740
    | exact resolve eq6740 eq6718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6740
  have eq6763 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6734 eq31
    | exact resolve eq31 eq6734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6810 : x = y ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq6763
    | exact resolve eq6763 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6763
  have eq6811 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq6810
  have eq6817 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq6811
       grind)
    | exact superpose eq6811 eq18
    | exact resolve eq18 eq6811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6818 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq6811
       grind)
    | exact superpose eq6811 eq24
    | exact resolve eq24 eq6811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6863 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq6818
    | exact resolve eq6818 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6818
  have eq7005 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq6715
       grind)
    | exact superpose eq6715 eq39
    | exact resolve eq39 eq6715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6715
  have eq7010 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq7005
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7005
    | exact resolve eq7005 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7005
  have eq7171 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq7010 eq856
    | (have j0 := eq856 (M.op (σ y) (σ x)) (M.op (σ x) (M.op X0 (σ x))) x
       grind)
    | exact resolve eq856 eq7010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq7172 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq7171 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7171
  have eq7173 : (M.op (σ y) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq7172 x
       have i₂ := eq949 sF2 x
       grind)
    | exact superpose eq949 eq7172
    | exact resolve eq7172 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7172
  have eq7177 : (M.op (σ y) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq7173
    | exact resolve eq7173 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7173
  have eq7774 : (σ (k x x)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq6694
       grind)
    | exact superpose eq6694 eq40
    | exact resolve eq40 eq6694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq7775 : x ≠ (k x x) ∨ (k y x) = (M.op y y) ∨ x = y ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq854 x y
       have i₂ := eq6694
       grind)
    | exact superpose eq6694 eq854
    | (have j0 := eq854 x y
       grind)
    | exact resolve eq854 eq6694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854 eq6694
  have eq7778 : x ≠ (k x x) ∨ (k y x) = (M.op y y) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq7775
  have eq7782 : x ≠ (k x x) ∨ (k y x) = (M.op y y) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq7778
       have r₂ := eq184
       grind)
    | exact resolve eq7778 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq7778
  have eq7783 : (σ (k x x)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7774
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7774
    | exact resolve eq7774 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7774
  have eq7785 : (k y x) = (k y y) ∨ x ≠ (k x x) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq7782
       have i₂ := eq943 y
       grind)
    | exact superpose eq943 eq7782
    | exact resolve eq7782 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7782
  have eq7786 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7783
       have i₂ := eq39 x
       grind)
    | exact superpose eq39 eq7783
    | exact resolve eq7783 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7783
  have eq7788 : (k y x) = (k y y) ∨ x ≠ (M.op x y) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq3323 eq7785
    | exact resolve eq7785 eq3323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3323 eq7785
  have eq7789 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7786
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7786
    | exact resolve eq7786 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7786
  have eq7791 : (k y x) = (k y y) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq7788
       have r₂ := eq6662
       grind)
    | exact resolve eq7788 eq6662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6662 eq7788
  have eq7792 : y = (k y y) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5161 eq7791
    | exact resolve eq7791 eq5161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5161 eq7791
  have eq7975 : ∀ X0 : G, (M.op x (M.op x y)) = (k (M.op X0 x) x) ∨ x = (M.op X0 x) ∨ x = (M.op x (M.op X0 x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6750 eq874
    | (have j0 := eq874 X0 x x
       grind)
    | exact resolve eq874 eq6750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874 eq6750
  have eq8185 : ∀ X0 : G, x = (M.op x (k x x)) ∨ (M.op x (M.op x y)) = (k (M.op X0 x) x) ∨ x = (M.op X0 x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7975 X0
       have i₂ := eq949 x X0
       grind)
    | exact superpose eq949 eq7975
    | (have j0 := eq7975 X0
       grind)
    | exact resolve eq7975 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7975
  have eq8262 : ∀ X0 : G, x = (M.op x (k x x)) ∨ (M.op x y) = (k (M.op X0 x) x) ∨ x = (M.op X0 x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6817 eq8185
    | (have j0 := eq8185 X0
       grind)
    | exact resolve eq8185 eq6817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6817 eq8185
  have eq8318 : ∀ X0 : G, x = (M.op x (k x (M.op x y))) ∨ (M.op x y) = (k (M.op X0 x) x) ∨ x = (M.op X0 x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6695 eq8262
    | (have j0 := eq8262 X0
       grind)
    | exact resolve eq8262 eq6695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8262
  have eq8355 : ∀ X0 : G, x = (M.op x y) ∨ (M.op x y) = (k (M.op X0 x) x) ∨ x = (M.op X0 x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6718 eq8318
    | (have j0 := eq8318 X0
       grind)
    | exact resolve eq8318 eq6718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8318
  have eq8356 : ∀ X0 : G, (M.op x y) = (k (M.op X0 x) x) ∨ x = (M.op x y) ∨ x = (M.op X0 x) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq8355 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8355
  have eq8519 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7789 eq888
    | exact resolve eq888 eq7789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq8527 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq8519
  have eq8549 : (M.op (M.op x y) y) = (M.op y y) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq951
       have i₂ := eq7792
       grind)
    | exact superpose eq7792 eq951
    | exact resolve eq951 eq7792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8568 : (k y y) = (M.op (M.op x y) y) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8549
       have i₂ := eq943 y
       grind)
    | exact superpose eq943 eq8549
    | exact resolve eq8549 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8549
  have eq8572 : y = (M.op (M.op x y) y) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq7792 eq8568
    | exact resolve eq8568 eq7792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8568
  have eq8805 : y = (k y (M.op x y)) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq8572 eq905
    | exact resolve eq905 eq8572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8824 : ∀ X0 : G, (M.op X0 y) ≠ (M.op y y) ∨ (M.op y y) = (k y (M.op X0 y)) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq8572 eq183
    | (have j0 := eq183 y x X0
       grind)
    | exact resolve eq183 eq8572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq8843 : ∀ X0 : G, (k y y) ≠ (M.op X0 y) ∨ (M.op y y) = (k y (M.op X0 y)) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq8824 X0
       have i₂ := eq943 y
       grind)
    | exact superpose eq943 eq8824
    | (have j0 := eq8824 X0
       grind)
    | exact resolve eq8824 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8824
  have eq8857 : y = (k y (M.op x y)) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6734 eq8805
    | exact resolve eq8805 eq6734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6734 eq8805
  have eq8870 : ∀ X0 : G, (k y y) = (k y (M.op X0 y)) ∨ (k y y) ≠ (M.op X0 y) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq8843 X0
       have i₂ := eq943 y
       grind)
    | exact superpose eq943 eq8843
    | (have j0 := eq8843 X0
       grind)
    | (have r₁ := eq8843 y
       have r₂ := eq943 y
       grind)
    | exact resolve eq8843 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8843
  have eq8880 : y = (k y (M.op x y)) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq187 eq8857
    | exact resolve eq8857 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8857
  have eq8887 : ∀ X0 : G, y = (k y (M.op X0 y)) ∨ (k y y) ≠ (M.op X0 y) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq7792 eq8870
    | (have j0 := eq8870 X0
       grind)
    | exact resolve eq8870 eq7792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8870
  have eq8897 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ y = (k y (M.op X0 y)) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq7792 eq8887
    | (have j0 := eq8887 X0
       grind)
    | exact resolve eq8887 eq7792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8887
  have eq9286 : ∀ X0 : G, (M.op y y) = (k y (M.op X0 y)) ∨ y = (M.op X0 y) ∨ (M.op X0 y) = (M.op (M.op X0 y) y) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq8572 eq863
    | (have j0 := eq863 y X0 x
       grind)
    | exact resolve eq863 eq8572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq9526 : ∀ X0 : G, (M.op y y) = (k y (M.op X0 y)) ∨ y = (M.op X0 y) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq9286 X0
       have j1 := eq13 y (M.op X0 y)
       grind)
    | (have r₁ := eq9286 y
       have r₂ := eq13 y y
       grind)
    | (have r₁ := eq9286 X0
       have r₂ := eq13 y (M.op X0 y)
       grind)
    | (have r₁ := eq9286 X0
       have r₂ := eq13 x y
       grind)
    | exact resolve eq9286 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9286
  have eq9607 : ∀ X0 : G, (k y y) = (k y (M.op X0 y)) ∨ y = (M.op X0 y) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq9526 X0
       have i₂ := eq943 y
       grind)
    | exact superpose eq943 eq9526
    | (have j0 := eq9526 X0
       grind)
    | exact resolve eq9526 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9526
  have eq9659 : ∀ X0 : G, y = (k y (M.op X0 y)) ∨ y = (M.op X0 y) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq7792 eq9607
    | (have j0 := eq9607 X0
       grind)
    | exact resolve eq9607 eq7792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7792 eq9607
  have eq9694 : ∀ X0 : G, y = (k y (M.op X0 y)) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq9659 X0
       have j1 := eq8897 X0
       grind)
    | (have r₁ := eq9659 X0
       have r₂ := eq8897 X0
       grind)
    | exact resolve eq9659 eq8897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8897 eq9659
  have eq9909 : y = (k y (k y (M.op x y))) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq905 eq9694
    | exact resolve eq9694 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905 eq9694
  have eq9931 : y = (k y (k y (M.op x y))) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8572 eq9909
    | exact resolve eq9909 eq8572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8572 eq9909
  have eq9943 : y = (k y (k y (M.op x y))) ∨ x = y ∨ y = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6811 eq9931
    | exact resolve eq9931 eq6811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6811 eq9931
  have eq9947 : y = (M.op (M.op x y) y) ∨ y = (k y (k y (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq187 eq9943
    | exact resolve eq9943 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq9943
  have eq9950 : y = (k y y) ∨ y = (M.op (M.op x y) y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8880 eq9947
    | exact resolve eq9947 eq8880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8880 eq9947
  have eq10425 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq8527 eq1022
    | exact resolve eq1022 eq8527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10548 : (M.op (M.op x y) y) = (M.op y y) ∨ y = (M.op (M.op x y) y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq951
       have i₂ := eq9950
       grind)
    | exact superpose eq9950 eq951
    | exact resolve eq951 eq9950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq10566 : (k y y) = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10548
       have i₂ := eq943 y
       grind)
    | exact superpose eq943 eq10548
    | exact resolve eq10548 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10548
  have eq10570 : y = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9950 eq10566
    | exact resolve eq10566 eq9950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9950 eq10566
  have eq10571 : y = (M.op (M.op x y) y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq10570
  have eq13121 : (M.op x y) = (k (M.op x (k x x)) x) ∨ x = (M.op x y) ∨ x = (M.op x (k x x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8356 (k x x)
       have i₂ := eq1022 x
       grind)
    | exact superpose eq1022 eq8356
    | exact resolve eq8356 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022 eq8356
  have eq13166 : (M.op x y) = (k (k (k x x) x) x) ∨ x = (M.op x y) ∨ x = (M.op x (k x x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1483 eq13121
    | (have j1 := eq1483 x
       grind)
    | exact resolve eq13121 eq1483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1483 eq13121
  have eq13182 : (M.op x y) = (k (k (k x (M.op x y)) x) x) ∨ x = (M.op x y) ∨ x = (M.op x (k x x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6695 eq13166
    | exact resolve eq13166 eq6695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13166
  have eq13196 : (M.op x y) = (k (k (k x (M.op x y)) x) x) ∨ x = (M.op x y) ∨ x = (M.op x (k x (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6695 eq13182
    | exact resolve eq13182 eq6695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6695 eq13182
  have eq13208 : (M.op x y) = (k (k (k x (M.op x y)) x) x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6718 eq13196
    | exact resolve eq13196 eq6718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6718 eq13196
  have eq13209 : (M.op x y) = (k (k (k x (M.op x y)) x) x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq13208
  have eq13232 : (σ (M.op x y)) = (k (σ (k (k x (M.op x y)) x)) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq13209 eq39
    | exact resolve eq39 eq13209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13209
  have eq13244 : (σ (M.op x y)) = (k (k (σ (k x (M.op x y))) (σ x)) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13232
       have i₂ := eq39 (k x sF0)
       grind)
    | exact superpose eq39 eq13232
    | exact resolve eq13232 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13232
  have eq13248 : (σ (M.op x y)) = (k (k (k (σ x) (σ (M.op x y))) (σ x)) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq41 eq13244
    | exact resolve eq13244 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq13244
  have eq13251 : (σ (M.op x y)) = (k (k (k (σ x) (σ (M.op x y))) (σ x)) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13248
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13248
    | exact resolve eq13248 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13248
  have eq13253 : (σ (M.op x y)) = (k (k (k (σ x) (σ (M.op x y))) (σ x)) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq13251
    | exact resolve eq13251 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13251
  have eq13254 : (σ y) = (k (k (k (σ x) (σ y)) (σ x)) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6863 eq13253
    | exact resolve eq13253 eq6863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13253
  have eq13255 : (σ y) = (k (k (k (σ x) (σ x)) (σ x)) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq7789 eq13254
    | exact resolve eq13254 eq7789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7789 eq13254
  have eq13256 : (σ y) = (k (k (M.op (σ x) (σ y)) (σ x)) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq8527 eq13255
    | exact resolve eq13255 eq8527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13255
  have eq13271 : (σ y) = (k (k (M.op (σ x) (σ y)) (σ x)) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq13256
  have eq13282 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq8527 eq7177
    | exact resolve eq7177 eq8527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13328 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq13282
  have eq13498 : (k (σ x) (σ x)) = (k (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq10425 eq2083
    | exact resolve eq2083 eq10425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10425
  have eq13502 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq8527 eq13498
    | exact resolve eq13498 eq8527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13498
  have eq128686 : (k (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq13328 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq13328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128739 : (σ y) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq13328
  have eq128740 : (k (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq128686
  have eq128811 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq128740
    | exact resolve eq128740 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128740
  have eq128812 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq128811
  have eq128859 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq7010 eq128812
    | exact resolve eq128812 eq7010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7010 eq128812
  have eq128898 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq128859
       have r₂ := eq128739
       grind)
    | exact resolve eq128859 eq128739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128739 eq128859
  have eq128980 : (M.op (σ x) (σ y)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq128898 eq949
    | exact resolve eq949 eq128898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq129036 : (M.op (σ x) (σ y)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq128980
    | exact resolve eq128980 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128980
  have eq129655 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq129036 eq7177
    | exact resolve eq7177 eq129036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7177 eq129036
  have eq129711 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq129655
  have eq129758 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq128898 eq129711
    | exact resolve eq129711 eq128898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128898 eq129711
  have eq129878 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq129758 eq27
    | exact resolve eq27 eq129758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129758
  have eq130014 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq129878
       have r₂ := eq6863
       grind)
    | exact resolve eq129878 eq6863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6863 eq129878
  have eq130027 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq130014 eq196
    | exact resolve eq196 eq130014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq130069 : (σ y) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq130014 eq13271
    | exact resolve eq13271 eq130014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13271
  have eq130072 : (σ x) = (k (σ x) (M.op (σ x) (M.op (σ x) (σ x)))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq130014 eq13502
    | exact resolve eq13502 eq130014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13502
  have eq130131 : (σ x) = (k (σ x) (M.op (σ x) (M.op (σ x) (σ x)))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq130072
  have eq130134 : (σ y) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq130069
  have eq130180 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq130131
       have i₂ := eq2083 sF2 sF2
       grind)
    | exact superpose eq2083 eq130131
    | exact resolve eq130131 eq2083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2083 eq130131
  have eq130183 : (σ y) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq8527 eq130134
    | exact resolve eq130134 eq8527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8527 eq130134
  have eq130212 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq130027
    | exact resolve eq130027 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130027
  have eq130225 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq130014 eq130183
    | exact resolve eq130183 eq130014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130183
  have eq130244 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq130014 eq130212
    | exact resolve eq130212 eq130014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130014 eq130212
  have eq130255 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq130180 eq130225
    | exact resolve eq130225 eq130180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130180 eq130225
  have eq130256 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq130255
  have eq130282 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq130244 eq130256
    | exact resolve eq130256 eq130244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130244 eq130256
  have eq130283 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq130282
  have eq130310 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq130283 eq31
    | exact resolve eq31 eq130283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130283
  have eq130382 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq130310
    | exact resolve eq130310 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130310
  have eq130383 : x = (M.op x y) ∨ x = y := by grind
  clear eq130382
  have eq130405 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq130383
       grind)
    | exact superpose eq130383 eq18
    | exact resolve eq18 eq130383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131215 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq130405 eq10571
    | exact resolve eq10571 eq130405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10571 eq130405
  have eq131379 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq131215
  have eq131721 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq131379 eq31
    | exact resolve eq31 eq131379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq131379
  have eq131793 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq131721
    | exact resolve eq131721 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq131721
  have eq131794 : y = (M.op x y) ∨ x = y := by grind
  clear eq131793
  have eq131986 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq131794
  have eq131994 : x = y := by
    first
    | (have r₁ := eq131986
       have r₂ := eq130383
       grind)
    | exact resolve eq131986 eq130383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130383 eq131986
  have eq133097 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq131994
       grind)
    | exact superpose eq131994 eq18
    | exact resolve eq18 eq131994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq133098 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq131994
       grind)
    | exact superpose eq131994 eq24
    | exact resolve eq24 eq131994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq131994
  have eq133142 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq133098
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq133098
    | exact resolve eq133098 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133098
  have eq133143 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq133097
       have i₂ := eq943 x
       grind)
    | exact superpose eq943 eq133097
    | exact resolve eq133097 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133097
  have eq133149 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq133142 eq26
    | exact resolve eq26 eq133142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq133142
  have eq133216 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq133149
       have i₂ := eq943 sF2
       grind)
    | exact superpose eq943 eq133149
    | exact resolve eq133149 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943 eq133149
  have eq133240 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq133143
       grind)
    | exact superpose eq133143 eq39
    | exact resolve eq39 eq133143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq133143
  have eq133247 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq133240
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq133240
    | exact resolve eq133240 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq133240
  have eq133250 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq133216 eq133247
    | exact resolve eq133247 eq133216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133216 eq133247
  have eq133252 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq133250
    | exact resolve eq133250 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq133250
  have eq133254 : False := by grind
  exact eq133254
