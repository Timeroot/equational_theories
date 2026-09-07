import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4279`: `x ◇ (x ◇ x) = y ◇ (z ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4279 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4279 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4279.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X2 X1)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X4 X3)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq8 x X3 X4
       have i₂ := eq8 x X0 X1
       grind)
    | (have i₁ := eq8 x X1 x
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X2 X3) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 (M.op X2 X3) X3
       have i₂ := eq8 X0 X3 X2
       grind)
    | (have i₁ := eq8 X0 (M.op X0 X0) X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq29 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25
    | exact resolve eq25 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq32 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op X3 X2)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 X3
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op X4 X5) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq18 X2 X3 (M.op X4 X5) X5
       have i₂ := eq18 X5 X4 X0 X1
       grind)
    | (have i₁ := eq18 X2 X3 (M.op X4 X5) X5
       have i₂ := eq18 X0 X1 X5 X4
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X2)) = (M.op (M.op X3 X4) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X2 (M.op X3 X4) X4
       have i₂ := eq18 X4 X3 X0 X1
       grind)
    | (have i₁ := eq8 X2 (M.op X3 X4) X4
       have i₂ := eq18 X0 X1 X4 X3
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq28
    | exact resolve eq28 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq33
    | exact resolve eq33 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq33 (τ X1) X0
       grind)
    | exact superpose eq33 eq17
    | (have j1 := eq33 (τ X1) X0
       grind)
    | exact resolve eq17 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq33 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq29 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq29
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq29 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq146 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq43
  have eq160 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq146 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq146
    | exact resolve eq146 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq212 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (k (M.op X1 (M.op X1 X1)) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    grind
  clear eq21
  have eq286 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14
       have i₂ := eq32 (σ y) (σ x) X0 X1
       grind)
    | exact superpose eq32 eq14
    | (have j1 := eq32 (σ y) (σ x) x x
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq312 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq286 X0 X1
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq286
    | (have j0 := eq286 X0 X1
       grind)
    | exact resolve eq286 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq419 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq160 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq160 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq160
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq160 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq535 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq35 x y
       grind)
    | exact superpose eq35 eq14
    | (have j1 := eq35 x y
       grind)
    | exact resolve eq14 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq9
    | (have j1 := eq35 X0 X1
       grind)
    | exact resolve eq9 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq584 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq35 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1370 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq584 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq584
    | (have j0 := eq584 (τ X0)
       grind)
    | exact resolve eq584 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq1372 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1370 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1370
    | (have j0 := eq1370 X0
       grind)
    | exact resolve eq1370 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370
  have eq1375 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1372 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1372
    | (have j0 := eq1372 X0
       grind)
    | exact resolve eq1372 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1372
  have eq1398 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq38
    | exact resolve eq38 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1461 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq10
    | (have j1 := eq38 X0 X1
       grind)
    | exact resolve eq10 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1489 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1398 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1398
    | (have j0 := eq1398 X0 X1
       grind)
    | exact resolve eq1398 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398
  have eq1511 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1375 (τ X0)
       have i₂ := eq70 X0 X0
       grind)
    | exact superpose eq70 eq1375
    | (have j0 := eq1375 (τ X0)
       grind)
    | exact resolve eq1375 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq1375
  have eq1513 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq82
    | exact resolve eq82 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq1554 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1513 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1513
    | (have j0 := eq1513 X0 X1
       grind)
    | exact resolve eq1513 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513
  have eq2039 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X2 X3 (σ X1) (σ X0)
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq18
    | (have j1 := eq79 X0 X1
       grind)
    | exact resolve eq18 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq2408 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq535
       have i₂ := eq1554 y x
       grind)
    | exact superpose eq1554 eq535
    | (have j1 := eq1554 y x
       grind)
    | (have r₁ := eq535
       have r₂ := eq1554 y x
       grind)
    | exact resolve eq535 eq1554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554
  have eq2409 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq535
       have i₂ := eq1489 y x
       grind)
    | exact superpose eq1489 eq535
    | (have j1 := eq1489 (σ y) (σ x)
       grind)
    | (have r₁ := eq535
       have r₂ := eq1489 y x
       grind)
    | exact resolve eq535 eq1489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535
  have eq2410 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2409
  have eq2411 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq2408
  have eq2423 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq160 x
       have i₂ := eq2410
       grind)
    | exact superpose eq2410 eq160
    | exact resolve eq160 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2456 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2423
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2423
    | exact resolve eq2423 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2423
  have eq2536 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq2456
       grind)
    | exact superpose eq2456 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq2456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2539 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1489 y x
       have i₂ := eq2456
       grind)
    | exact superpose eq2456 eq1489
    | (have j0 := eq1489 y x
       grind)
    | exact resolve eq1489 eq2456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489 eq2456
  have eq2540 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq2539
  have eq2541 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq2536
  have eq2591 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq554 x x
       have i₂ := eq2410
       grind)
    | exact superpose eq2410 eq554
    | exact resolve eq554 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq2633 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2591
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2591
    | exact resolve eq2591 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2591
  have eq2646 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 y x
       have i₂ := eq2541
       grind)
    | exact superpose eq2541 eq18
    | exact resolve eq18 eq2541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3776 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq160 x
       have i₂ := eq2411
       grind)
    | exact superpose eq2411 eq160
    | exact resolve eq160 eq2411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq2411
  have eq3824 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq3776
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3776
    | exact resolve eq3776 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3776
  have eq3825 : x = (k x y) := by grind
  clear eq3824
  have eq5341 : (M.op (σ x) (σ y)) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2646 (σ x) (σ x)
       have i₂ := eq2410
       grind)
    | exact superpose eq2410 eq2646
    | exact resolve eq2646 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5461 : (M.op (σ x) (σ y)) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq5341
  have eq5885 : (σ (M.op x y)) ≠ (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq5461
       grind)
    | exact superpose eq5461 eq14
    | exact resolve eq14 eq5461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5461
  have eq6348 : (σ x) ≠ (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5885
       have i₂ := eq2540
       grind)
    | exact superpose eq2540 eq5885
    | exact resolve eq5885 eq2540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2540 eq5885
  have eq6349 : (σ x) ≠ (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq6348
  have eq8009 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq90
    | (have j0 := eq90 X1 (σ X0)
       grind)
    | exact resolve eq90 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq8086 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8009 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq8009
    | (have j0 := eq8009 X0 X1
       grind)
    | exact resolve eq8009 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8009
  have eq21291 : ∀ X0 : G, (τ (σ X0)) ≠ (τ (M.op (σ X0) (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1511 (σ X0)
       have i₂ := eq419 (σ X0) X0
       grind)
    | exact superpose eq419 eq1511
    | (have j0 := eq1511 (σ X0)
       have j1 := eq419 (σ X0) X0
       grind)
    | exact resolve eq1511 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq21315 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq21291 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq21291
    | (have j0 := eq21291 X0
       grind)
    | exact resolve eq21291 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21291
  have eq21323 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq21315 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq21315
    | (have j0 := eq21315 X0
       grind)
    | exact resolve eq21315 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21315
  have eq21325 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq21323 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq21323
    | (have j0 := eq21323 X0
       grind)
    | exact resolve eq21323 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21323
  have eq21327 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq21325 X0
       have j1 := eq85 X0 X0
       grind)
    | (have r₁ := eq21325 x
       have r₂ := eq85 x x
       grind)
    | exact resolve eq21325 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq21325
  have eq22214 : x ≠ (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq21327 x
       have i₂ := eq2410
       grind)
    | exact superpose eq2410 eq21327
    | (have j0 := eq21327 x
       grind)
    | exact resolve eq21327 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21327
  have eq22240 : x ≠ y ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq22214
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq22214
    | exact resolve eq22214 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22214
  have eq25535 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq2633
       grind)
    | exact superpose eq2633 eq9
    | exact resolve eq9 eq2633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2633
  have eq25604 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq25535
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq25535
    | exact resolve eq25535 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25535
  have eq26593 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq33 x x
       have i₂ := eq25604
       grind)
    | exact superpose eq25604 eq33
    | exact resolve eq33 eq25604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq25604
  have eq26606 : y = (M.op x x) ∨ x = y := by grind
  clear eq26593
  have eq27635 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 X0)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 x x
       have i₂ := eq26606
       grind)
    | exact superpose eq26606 eq18
    | exact resolve eq18 eq26606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26606
  have eq28743 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) (M.op x y)) ∨ x = y ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq27635 (M.op X0 X1) X1
       have i₂ := eq27635 X1 X0
       grind)
    | exact superpose eq27635 eq27635
    | exact resolve eq27635 eq27635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27635
  have eq29070 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) (M.op x y)) ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq28743 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28743
  have eq32461 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y := by grind
  clear eq29070
  have eq33274 : x = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq32461
       have i₂ := eq2541
       grind)
    | exact superpose eq2541 eq32461
    | exact resolve eq32461 eq2541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2541 eq32461
  have eq33332 : x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq33274
       have r₂ := eq22240
       grind)
    | exact resolve eq33274 eq22240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22240 eq33274
  have eq34362 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq584 x
       have i₂ := eq33332
       grind)
    | exact superpose eq33332 eq584
    | (have j0 := eq584 x
       grind)
    | exact resolve eq584 eq33332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq33332
  have eq34386 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq34362
  have eq41020 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2410
       have i₂ := eq34386
       grind)
    | exact superpose eq34386 eq2410
    | exact resolve eq2410 eq34386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2410
  have eq41169 : (M.op (σ x) (σ x)) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2646 (σ x) (σ x)
       have i₂ := eq34386
       grind)
    | exact superpose eq34386 eq2646
    | exact resolve eq2646 eq34386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2646
  have eq41173 : (M.op (σ x) (σ x)) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq41169
  have eq41178 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq41020
  have eq50975 : (σ x) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq34386
       have i₂ := eq41173
       grind)
    | exact superpose eq41173 eq34386
    | exact resolve eq34386 eq41173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34386 eq41173
  have eq51084 : (σ x) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq50975
  have eq51093 : y = (M.op x x) := by
    first
    | (have r₁ := eq51084
       have r₂ := eq6349
       grind)
    | exact resolve eq51084 eq6349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6349 eq51084
  have eq52251 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq212 X0 x
       have i₂ := eq51093
       grind)
    | exact superpose eq51093 eq212
    | exact resolve eq212 eq51093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq52278 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 x x
       have i₂ := eq51093
       grind)
    | exact superpose eq51093 eq18
    | exact resolve eq18 eq51093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq52282 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X3) (M.op x y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 x x X0 X1 X2 X3
       have i₂ := eq51093
       grind)
    | exact superpose eq51093 eq57
    | exact resolve eq57 eq51093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq52286 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op X1 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 X1 X2 X0 x x
       have i₂ := eq51093
       grind)
    | exact superpose eq51093 eq69
    | exact resolve eq69 eq51093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq51093
  have eq52362 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq52251 x
       have i₂ := eq52278 x x
       grind)
    | exact superpose eq52278 eq52251
    | exact resolve eq52251 eq52278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52251
  have eq53771 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq52278 (M.op X0 X1) X1
       have i₂ := eq52278 X1 X0
       grind)
    | exact superpose eq52278 eq52278
    | exact resolve eq52278 eq52278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57047 : (τ (M.op x y)) ≠ (τ (M.op x y)) ∨ (τ (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) := by
    first
    | (have i₁ := eq1511 (M.op x y)
       have i₂ := eq52362
       grind)
    | exact superpose eq52362 eq1511
    | (have j0 := eq1511 (M.op x y)
       grind)
    | exact resolve eq1511 eq52362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511 eq52362
  have eq57061 : (τ (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) := by grind
  clear eq57047
  have eq63093 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq1461 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1461
  have eq63094 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq63093 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq63093
    | (have j0 := eq63093 X0
       grind)
    | exact resolve eq63093 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63093
  have eq63140 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq63094 (σ X0)
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq63094
    | (have j0 := eq63094 (σ X0)
       grind)
    | exact resolve eq63094 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63094
  have eq63150 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq63140 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq63140
    | (have j0 := eq63140 X0
       grind)
    | exact resolve eq63140 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63140
  have eq71931 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq63150 X0
       have i₂ := eq8086 X0 X0
       grind)
    | exact superpose eq8086 eq63150
    | (have j0 := eq63150 X0
       have j1 := eq8086 X0 X0
       grind)
    | (have r₁ := eq63150 x
       have r₂ := eq8086 x x
       grind)
    | exact resolve eq63150 eq8086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8086 eq63150
  have eq71938 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq71931 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71931
  have eq71968 : (σ x) = (σ y) ∨ y = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq71938 x
       have i₂ := eq41178
       grind)
    | exact superpose eq41178 eq71938
    | exact resolve eq71938 eq41178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41178 eq71938
  have eq72004 : y = (k x x) ∨ (σ x) = (σ y) := by grind
  clear eq71968
  have eq74048 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq52282 (τ (M.op x y)) (τ (M.op x y)) X0 X1
       have i₂ := eq57061
       grind)
    | exact superpose eq57061 eq52282
    | exact resolve eq52282 eq57061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52282
  have eq74054 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (τ (M.op x y)) (τ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq52286 X0 (τ (M.op x y)) (τ (M.op x y))
       have i₂ := eq57061
       grind)
    | exact superpose eq57061 eq52286
    | exact resolve eq52286 eq57061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52286
  have eq74056 : (M.op x y) = (M.op (τ (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq53771 (τ (M.op x y)) (τ (M.op x y))
       have i₂ := eq57061
       grind)
    | exact superpose eq57061 eq53771
    | exact resolve eq53771 eq57061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74059 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (τ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq74054 X0
       have i₂ := eq57061
       grind)
    | exact superpose eq57061 eq74054
    | exact resolve eq74054 eq57061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74054
  have eq74065 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op x y)) = (τ (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq74048 X0 X1
       have i₂ := eq57061
       grind)
    | exact superpose eq57061 eq74048
    | exact resolve eq74048 eq57061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57061 eq74048
  have eq74173 : (M.op x y) = (M.op y (τ (M.op x y))) := by
    first
    | (have i₁ := eq74059 x
       have i₂ := eq52278 x x
       grind)
    | exact superpose eq52278 eq74059
    | exact resolve eq74059 eq52278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74059
  have eq74177 : (M.op x y) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq74065 x x
       have i₂ := eq53771 x x
       grind)
    | exact superpose eq53771 eq74065
    | exact resolve eq74065 eq53771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53771 eq74065
  have eq74351 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq74177
       grind)
    | exact superpose eq74177 eq10
    | exact resolve eq10 eq74177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74177
  have eq74568 : (σ (M.op x y)) ≠ (M.op (τ (M.op x y)) (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq312 (τ (M.op x y)) y
       have i₂ := eq74173
       grind)
    | exact superpose eq74173 eq312
    | exact resolve eq312 eq74173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312 eq74173
  have eq74622 : (M.op x y) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq74568
       have i₂ := eq74056
       grind)
    | exact superpose eq74056 eq74568
    | exact resolve eq74568 eq74056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74056 eq74568
  have eq74668 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have r₁ := eq74622
       have r₂ := eq74351
       grind)
    | exact resolve eq74622 eq74351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74622
  have eq74681 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74668
       have i₂ := eq3825
       grind)
    | exact superpose eq3825 eq74668
    | exact resolve eq74668 eq3825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3825 eq74668
  have eq74727 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq74681
       grind)
    | exact superpose eq74681 eq14
    | exact resolve eq14 eq74681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74843 : (M.op x y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq52278 (σ y) (σ x)
       have i₂ := eq74681
       grind)
    | exact superpose eq74681 eq52278
    | exact resolve eq52278 eq74681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74960 : (M.op x y) ≠ (σ x) := by
    first
    | (have i₁ := eq74727
       have i₂ := eq74351
       grind)
    | exact superpose eq74351 eq74727
    | exact resolve eq74727 eq74351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74351 eq74727
  have eq76765 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X1 X0)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq2039 x x x x
       have i₂ := eq72004
       grind)
    | exact superpose eq72004 eq2039
    | exact resolve eq2039 eq72004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2039 eq72004
  have eq76809 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X1 X0)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have j0 := eq76765 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76765
  have eq76821 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq76809 x x
       have i₂ := eq52278 x x
       grind)
    | exact superpose eq52278 eq76809
    | exact resolve eq76809 eq52278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52278 eq76809
  have eq76839 : (M.op x y) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq76821
       have i₂ := eq74681
       grind)
    | exact superpose eq74681 eq76821
    | exact resolve eq76821 eq74681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76821
  have eq76841 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq76839
       have r₂ := eq74960
       grind)
    | exact resolve eq76839 eq74960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76839
  have eq76843 : (M.op x y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq74843
       have i₂ := eq76841
       grind)
    | exact superpose eq76841 eq74843
    | exact resolve eq74843 eq76841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74843
  have eq76844 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq74681
       have i₂ := eq76841
       grind)
    | exact superpose eq76841 eq74681
    | exact resolve eq74681 eq76841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74681 eq76841
  have eq76946 : (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq76843
       have i₂ := eq76844
       grind)
    | exact superpose eq76844 eq76843
    | exact resolve eq76843 eq76844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76843 eq76844
  have eq76948 : False := by grind
  exact eq76948

/-- `Equation4279`: `x ◇ (x ◇ x) = y ◇ (z ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pyx_Equation4279 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4279 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4279.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X2 X1)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X4 X3)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq8 x X3 X4
       have i₂ := eq8 x X0 X1
       grind)
    | (have i₁ := eq8 x X1 x
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X2 X3) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 (M.op X2 X3) X3
       have i₂ := eq8 X0 X3 X2
       grind)
    | (have i₁ := eq8 X0 (M.op X0 X0) X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op X3 X2)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 X3
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 (M.op X0 X0) X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq33 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  have eq42 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq45 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq36
    | exact resolve eq36 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq57 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op X4 X5) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq18 X2 X3 (M.op X4 X5) X5
       have i₂ := eq18 X5 X4 X0 X1
       grind)
    | (have i₁ := eq18 X2 X3 (M.op X4 X5) X5
       have i₂ := eq18 X0 X1 X5 X4
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  clear eq27
  have eq80 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq31
    | exact resolve eq31 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq31 (τ X1) X0
       grind)
    | exact superpose eq31 eq16
    | (have j1 := eq31 (τ X1) X0
       grind)
    | exact resolve eq16 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq95 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X1 X0
       have i₂ := eq12 (σ X1) X0
       grind)
    | exact superpose eq12 eq42
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq144 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X1
       have i₂ := eq12 X0 (τ X1)
       grind)
    | (have i₁ := eq45 X0
       have i₂ := eq12 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact superpose eq12 eq45
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq212 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (k (M.op X0 (M.op X0 X0)) (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    grind
  clear eq21
  have eq286 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq14
       have i₂ := eq30 (σ y) (σ x) X0 X1
       grind)
    | exact superpose eq30 eq14
    | (have j1 := eq30 (σ y) (σ x) x x
       grind)
    | exact resolve eq14 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq312 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    intro X0 X1
    first
    | (have i₁ := eq286 X0 X1
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq286
    | (have j0 := eq286 X0 X1
       grind)
    | exact resolve eq286 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq535 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq33 x y
       grind)
    | exact superpose eq33 eq14
    | (have j1 := eq33 x y
       grind)
    | exact resolve eq14 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq9
    | (have j1 := eq33 X0 X1
       grind)
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq584 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq33 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq1029 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (k (M.op X0 (M.op X1 X0)) (M.op X2 (M.op X3 X2))) := by
    intro X0 X1 X2 X3
    grind
  clear eq57
  have eq1398 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1461 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq10
    | (have j1 := eq34 X0 X1
       grind)
    | exact resolve eq10 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq1489 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1398 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1398
    | (have j0 := eq1398 X0 X1
       grind)
    | exact resolve eq1398 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398
  have eq1513 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq86
    | exact resolve eq86 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1554 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1513 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1513
    | (have j0 := eq1513 X0 X1
       grind)
    | exact resolve eq1513 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513
  have eq2038 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X2 X3 (σ X0) (σ X1)
       have i₂ := eq81 X0 X1
       grind)
    | exact superpose eq81 eq18
    | (have j1 := eq81 X0 X1
       grind)
    | exact resolve eq18 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq2338 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) ≠ (σ (M.op X0 (M.op X0 X0))) ∨ (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq584 (M.op X0 (M.op X0 X0))
       have i₂ := eq212 X0 X0
       grind)
    | exact superpose eq212 eq584
    | (have j0 := eq584 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq584 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq2345 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq2338 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2338
  have eq2408 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq535
       have i₂ := eq1554 y x
       grind)
    | exact superpose eq1554 eq535
    | (have j1 := eq1554 y x
       grind)
    | (have r₁ := eq535
       have r₂ := eq1554 y x
       grind)
    | exact resolve eq535 eq1554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554
  have eq2409 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq535
       have i₂ := eq1489 y x
       grind)
    | exact superpose eq1489 eq535
    | (have j1 := eq1489 (σ y) (σ x)
       grind)
    | (have r₁ := eq535
       have r₂ := eq1489 y x
       grind)
    | exact resolve eq535 eq1489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535
  have eq2410 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2409
  have eq2411 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k y x) := by grind
  clear eq2408
  have eq2423 : x = (k (τ (σ y)) x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq80 x
       have i₂ := eq2410
       grind)
    | exact superpose eq2410 eq80
    | exact resolve eq80 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2456 : x = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2423
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2423
    | exact resolve eq2423 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2423
  have eq2537 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq2456
       grind)
    | exact superpose eq2456 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq2456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2540 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1489 y x
       have i₂ := eq2456
       grind)
    | exact superpose eq2456 eq1489
    | (have j0 := eq1489 y x
       grind)
    | exact resolve eq1489 eq2456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489 eq2456
  have eq2541 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq2540
  have eq2542 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq2537
  have eq2592 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq554 x x
       have i₂ := eq2410
       grind)
    | exact superpose eq2410 eq554
    | exact resolve eq554 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq2634 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2592
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2592
    | exact resolve eq2592 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2592
  have eq2647 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 y x
       have i₂ := eq2542
       grind)
    | exact superpose eq2542 eq18
    | exact resolve eq18 eq2542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2542
  have eq3777 : x = (k (τ (σ y)) x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq80 x
       have i₂ := eq2411
       grind)
    | exact superpose eq2411 eq80
    | exact resolve eq80 eq2411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2411
  have eq3825 : x = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq3777
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3777
    | exact resolve eq3777 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3777
  have eq3826 : x = (k y x) := by grind
  clear eq3825
  have eq5343 : (M.op (σ x) (σ y)) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2647 (σ x) (σ x)
       have i₂ := eq2410
       grind)
    | exact superpose eq2410 eq2647
    | exact resolve eq2647 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5463 : (M.op (σ x) (σ y)) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq5343
  have eq5887 : (σ (M.op x y)) ≠ (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq5463
       grind)
    | exact superpose eq5463 eq14
    | exact resolve eq14 eq5463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5463
  have eq6350 : (σ x) ≠ (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5887
       have i₂ := eq2541
       grind)
    | exact superpose eq2541 eq5887
    | exact resolve eq5887 eq2541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2541 eq5887
  have eq6351 : (σ x) ≠ (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq6350
  have eq9349 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq144 X1 (σ X0)
       grind)
    | exact superpose eq144 eq13
    | (have j1 := eq144 X1 (σ X0)
       grind)
    | exact resolve eq13 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9404 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9349 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq9349
    | (have j0 := eq9349 X0 X1
       grind)
    | exact resolve eq9349 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9349
  have eq22942 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq2634
       grind)
    | exact superpose eq2634 eq9
    | exact resolve eq9 eq2634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2634
  have eq23003 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq22942
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq22942
    | exact resolve eq22942 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22942
  have eq23528 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq31 x x
       have i₂ := eq23003
       grind)
    | exact superpose eq23003 eq31
    | exact resolve eq31 eq23003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq23003
  have eq23541 : y = (M.op x x) ∨ x = y := by grind
  clear eq23528
  have eq48022 : (τ (σ y)) = (k x (τ (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq95 (σ x) x
       have i₂ := eq2410
       grind)
    | exact superpose eq2410 eq95
    | exact resolve eq95 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48412 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (k X0 (τ (σ X1))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq80 X1
       have i₂ := eq95 (σ X1) X0
       grind)
    | exact superpose eq95 eq80
    | (have j1 := eq95 (σ X1) X0
       grind)
    | exact resolve eq80 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq95
  have eq48626 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k X0 (τ (σ X1))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq48412 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq48412
    | (have j0 := eq48412 X0 X1
       grind)
    | exact resolve eq48412 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48412
  have eq48676 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq48022
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq48022
    | exact resolve eq48022 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48022
  have eq48714 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48626 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq48626
    | (have j0 := eq48626 X0 X1
       grind)
    | exact resolve eq48626 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48626
  have eq48721 : y = (k x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq48676
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq48676
    | exact resolve eq48676 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48676
  have eq52920 : (k x x) = (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq48714 x x
       have i₂ := eq2410
       grind)
    | exact superpose eq2410 eq48714
    | (have j0 := eq48714 x x
       grind)
    | exact resolve eq48714 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2410 eq48714
  have eq53001 : y = (k x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq52920
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq52920
    | exact resolve eq52920 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52920
  have eq53855 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9404 x x
       have i₂ := eq48721
       grind)
    | exact superpose eq48721 eq9404
    | exact resolve eq9404 eq48721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9404 eq48721
  have eq53860 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq53855
  have eq60736 : x ≠ y ∨ x = (k x x) ∨ y = (M.op x x) := by grind
  clear eq53001
  have eq60758 : x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq60736
       have r₂ := eq23541
       grind)
    | exact resolve eq60736 eq23541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23541 eq60736
  have eq66150 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq584 x
       have i₂ := eq60758
       grind)
    | exact superpose eq60758 eq584
    | (have j0 := eq584 x
       grind)
    | exact resolve eq584 eq60758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60758
  have eq66178 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq66150
  have eq68373 : ∀ X0 : G, (k X0 (σ (τ X0))) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq1461 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1461
  have eq68374 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq68373 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq68373
    | (have j0 := eq68373 X0
       grind)
    | exact resolve eq68373 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68373
  have eq68607 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq68374 (σ X0)
       have i₂ := eq144 X0 (σ X0)
       grind)
    | exact superpose eq144 eq68374
    | (have j0 := eq68374 (σ X0)
       have j1 := eq144 X0 (σ X0)
       grind)
    | (have r₁ := eq68374 (σ X0)
       have r₂ := eq144 X0 (σ X0)
       grind)
    | exact resolve eq68374 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq68374
  have eq68617 : ∀ X0 : G, (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) X0) := by
    intro X0
    first
    | (have j0 := eq68607 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68607
  have eq68622 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq68617 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq68617
    | (have j0 := eq68617 X0
       grind)
    | exact resolve eq68617 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68617
  have eq68630 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq68622 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq68622
    | (have j0 := eq68622 X0
       grind)
    | exact resolve eq68622 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68622
  have eq71018 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 X0))) ≠ (σ (M.op X0 (M.op X1 X0))) ∨ (σ (M.op X0 (M.op X1 X0))) = (M.op (σ (M.op X0 (M.op X1 X0))) (σ (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq584 (M.op X0 (M.op X1 X0))
       have i₂ := eq1029 X0 X1 X0 X1
       grind)
    | exact superpose eq1029 eq584
    | (have j0 := eq584 (M.op X0 (M.op X1 X0))
       grind)
    | exact resolve eq584 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq1029
  have eq71074 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 X0))) = (M.op (σ (M.op X0 (M.op X1 X0))) (σ (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq71018 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71018
  have eq71292 : (M.op (σ x) (σ x)) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2647 (σ x) (σ x)
       have i₂ := eq66178
       grind)
    | exact superpose eq66178 eq2647
    | exact resolve eq2647 eq66178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2647
  have eq71297 : (M.op (σ x) (σ x)) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq71292
  have eq74258 : (σ x) = (σ y) ∨ y = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq68630 x
       have i₂ := eq53860
       grind)
    | exact superpose eq53860 eq68630
    | exact resolve eq68630 eq53860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53860 eq68630
  have eq74456 : y = (k x x) ∨ (σ x) = (σ y) := by grind
  clear eq74258
  have eq88753 : (σ x) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq66178
       have i₂ := eq71297
       grind)
    | exact superpose eq71297 eq66178
    | exact resolve eq66178 eq71297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66178 eq71297
  have eq88976 : (σ x) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq88753
  have eq88990 : y = (M.op x x) := by
    first
    | (have r₁ := eq88976
       have r₂ := eq6351
       grind)
    | exact resolve eq88976 eq6351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6351 eq88976
  have eq90456 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 x x
       have i₂ := eq88990
       grind)
    | exact superpose eq88990 eq18
    | exact resolve eq18 eq88990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq88990
  have eq126083 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X1 X0)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq2038 x x x x
       have i₂ := eq74456
       grind)
    | exact superpose eq74456 eq2038
    | exact resolve eq2038 eq74456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2038 eq74456
  have eq126711 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X1 X0)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have j0 := eq126083 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126083
  have eq126919 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq126711 x x
       have i₂ := eq90456 x x
       grind)
    | exact superpose eq90456 eq126711
    | exact resolve eq126711 eq90456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126711
  have eq129172 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    intro X0
    first
    | (have i₁ := eq312 (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))
       have i₂ := eq2345 X0
       grind)
    | exact superpose eq2345 eq312
    | exact resolve eq312 eq2345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq129217 : ∀ X0 : G, (M.op x y) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq90456 (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))
       have i₂ := eq2345 X0
       grind)
    | exact superpose eq2345 eq90456
    | exact resolve eq90456 eq2345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129248 : ∀ X0 : G, (M.op x y) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq129217 X0
       have i₂ := eq71074 X0 X0
       grind)
    | exact superpose eq71074 eq129217
    | exact resolve eq129217 eq71074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71074 eq129217
  have eq129292 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op X0 (M.op X0 X0))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    intro X0
    first
    | (have i₁ := eq129172 X0
       have i₂ := eq2345 X0
       grind)
    | exact superpose eq2345 eq129172
    | exact resolve eq129172 eq2345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2345 eq129172
  have eq129667 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq129248 x
       have i₂ := eq90456 x x
       grind)
    | exact superpose eq90456 eq129248
    | exact resolve eq129248 eq90456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129248
  have eq129710 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq129292 x
       have i₂ := eq90456 x x
       grind)
    | exact superpose eq90456 eq129292
    | exact resolve eq129292 eq90456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129292
  have eq129711 : (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq129710
  have eq130062 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq129711
       have i₂ := eq3826
       grind)
    | exact superpose eq3826 eq129711
    | exact resolve eq129711 eq3826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3826 eq129711
  have eq130611 : (M.op x y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq90456 (σ y) (σ x)
       have i₂ := eq130062
       grind)
    | exact superpose eq130062 eq90456
    | exact resolve eq90456 eq130062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90456 eq130062
  have eq181201 : (M.op x y) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq126919
       grind)
    | exact superpose eq126919 eq14
    | exact resolve eq14 eq126919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126919
  have eq181333 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq181201
       have r₂ := eq129667
       grind)
    | exact resolve eq181201 eq129667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181201
  have eq181369 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq181333
       grind)
    | exact superpose eq181333 eq14
    | exact resolve eq14 eq181333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181374 : (M.op x y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq130611
       have i₂ := eq181333
       grind)
    | exact superpose eq181333 eq130611
    | exact resolve eq130611 eq181333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130611 eq181333
  have eq181549 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq181369
       have i₂ := eq181374
       grind)
    | exact superpose eq181374 eq181369
    | exact resolve eq181369 eq181374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181369 eq181374
  have eq181567 : False := by grind
  exact eq181567

/-- `Equation4286`: `x ◇ (x ◇ y) = x ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation4286 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4286 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4286.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X2 X0)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X3 X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X0 x X3
       have i₂ := eq8 X0 x X1
       grind)
    | (have i₁ := eq8 x x x
       have i₂ := eq8 x X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X0 X2 x
       grind)
    | (have i₁ := eq8 X1 X1 X1
       have i₂ := eq8 X1 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq33 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq36 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30
    | exact resolve eq30 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq145 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq33 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq148 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (k X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq145 X0 (M.op X0 X2)
       have i₂ := eq25 X0 X2 X1
       grind)
    | (have i₁ := eq145 X0 (M.op X0 X2)
       have i₂ := eq25 X0 X1 X2
       grind)
    | exact superpose eq25 eq145
    | (have j0 := eq145 X0 (M.op X0 X2)
       grind)
    | (have r₁ := eq145 X0 (M.op X0 (M.op X0 X2))
       have r₂ := eq25 X0 (M.op X0 X2) X2
       grind)
    | (have r₁ := eq145 X0 (M.op X0 (M.op X0 X1))
       have r₂ := eq25 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq145 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq409 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq36 x y
       grind)
    | exact superpose eq36 eq14
    | (have j1 := eq36 x y
       grind)
    | exact resolve eq14 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op X2 (σ X0))) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (σ X0) (σ X1) X2
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq8
    | (have j1 := eq36 X0 X1
       grind)
    | exact resolve eq8 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq9
    | (have j1 := eq36 X0 X1
       grind)
    | exact resolve eq9 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq36 X0 X2
       grind)
    | exact superpose eq36 eq13
    | (have j1 := eq36 X0 X2
       grind)
    | exact resolve eq13 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq871 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq39
    | exact resolve eq39 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq934 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq871 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq871
    | (have j0 := eq871 X0 X1
       grind)
    | exact resolve eq871 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq1533 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq409
       have i₂ := eq934 y x
       grind)
    | exact superpose eq934 eq409
    | (have j1 := eq934 (σ y) (σ x)
       grind)
    | (have r₁ := eq409
       have r₂ := eq934 y x
       grind)
    | exact resolve eq409 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq1534 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1533
  have eq11711 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) (M.op X2 (σ (τ X0)))) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq412 (τ X0) (τ X1) X2
       have i₂ := eq73 X1 X0
       grind)
    | exact superpose eq73 eq412
    | (have j0 := eq412 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq412 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq11902 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) (M.op X2 (σ (τ X0)))) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11711 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq11711
    | (have j0 := eq11711 X0 X1 X2
       grind)
    | exact resolve eq11711 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11711
  have eq11907 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (M.op X0 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11902 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11902
    | (have j0 := eq11902 X0 X1 X2
       grind)
    | exact resolve eq11902 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11902
  have eq11908 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op X0 (M.op X2 X0)) = (M.op X0 (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11907 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11907
    | (have j0 := eq11907 X0 X1 X2
       grind)
    | exact resolve eq11907 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11907
  have eq11909 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (M.op X0 (k X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11908 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq11908
    | (have j0 := eq11908 X0 X1 X2
       grind)
    | exact resolve eq11908 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11908
  have eq14544 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  clear eq425
  have eq100924 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq148 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq101189 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq100924 X1 X1
       have i₂ := eq20 X1 X1 x
       grind)
    | (have i₁ := eq100924 x x
       have i₂ := eq20 x X1 x
       grind)
    | exact superpose eq20 eq100924
    | exact resolve eq100924 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151127 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq14544 (τ X1) (τ X0)
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq14544
    | exact resolve eq14544 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq151530 : (σ y) = (σ (k x x)) ∨ (σ y) = (σ (k x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14544 x x
       have i₂ := eq1534
       grind)
    | exact superpose eq1534 eq14544
    | exact resolve eq14544 eq1534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1534
  have eq151583 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 X1)
       have i₂ := eq14544 X0 X1
       grind)
    | exact superpose eq14544 eq9
    | (have j1 := eq14544 X0 X1
       grind)
    | exact resolve eq9 eq14544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152242 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq14544 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14544
  have eq152243 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq152242 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152242
  have eq152250 : (σ y) = (σ (k x x)) ∨ y = (M.op x x) := by grind
  clear eq151530
  have eq152689 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (k X0 X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq151583 X0 X1
       have i₂ := eq152243 X0
       grind)
    | exact superpose eq152243 eq151583
    | (have j0 := eq151583 X0 X1
       grind)
    | exact resolve eq151583 eq152243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151583
  have eq152968 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (k (τ X0) (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq151127 X0 X1
       have i₂ := eq152243 (τ X0)
       grind)
    | exact superpose eq152243 eq151127
    | (have j0 := eq151127 X0 X1
       grind)
    | exact resolve eq151127 eq152243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151127
  have eq153199 : ∀ X0 X1 : G, (k X0 X1) = (k X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq152689 X0 X1
       have i₂ := eq9 (k X0 X0)
       grind)
    | exact superpose eq9 eq152689
    | (have j0 := eq152689 X0 X1
       grind)
    | exact resolve eq152689 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152689
  have eq153330 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (k (σ (τ X0)) X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq152968 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq152968
    | (have j0 := eq152968 X0 X1
       grind)
    | exact resolve eq152968 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152968
  have eq153503 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq153330 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq153330
    | (have j0 := eq153330 X0 X1
       grind)
    | exact resolve eq153330 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153330
  have eq153585 : ∀ X0 X1 : G, (k X0 X1) = (k X0 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq153503 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq153503
    | (have j0 := eq153503 X0 X1
       grind)
    | exact resolve eq153503 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153503
  have eq153627 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq153585 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq153585
    | (have j0 := eq153585 X0 X1
       grind)
    | exact resolve eq153585 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153585
  have eq153647 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq153627 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq153627
    | (have j0 := eq153627 X0 X1
       grind)
    | exact resolve eq153627 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153627
  have eq153652 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq153647 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq153647
    | (have j0 := eq153647 X0 X1
       grind)
    | exact resolve eq153647 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153647
  have eq153701 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq152243 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq152243
    | exact resolve eq152243 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153797 : ∀ X0 X1 : G, (τ (σ (k X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq423 X0 X1
       have i₂ := eq152243 X0
       grind)
    | exact superpose eq152243 eq423
    | (have j0 := eq423 X0 X1
       grind)
    | exact resolve eq423 eq152243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq153855 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 (σ X0))) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X0) X1 (σ X0)
       have i₂ := eq152243 X0
       grind)
    | exact superpose eq152243 eq20
    | exact resolve eq20 eq152243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152243
  have eq154065 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq153797 X0 X1
       have i₂ := eq9 (k X0 X0)
       grind)
    | exact superpose eq9 eq153797
    | (have j0 := eq153797 X0 X1
       grind)
    | exact resolve eq153797 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153797
  have eq154103 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq153701 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq153701
    | exact resolve eq153701 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq153701
  have eq154139 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq154103 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq154103
    | exact resolve eq154103 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154103
  have eq164760 : (k x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq152250
       grind)
    | exact superpose eq152250 eq9
    | exact resolve eq9 eq152250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152250
  have eq165056 : y = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq164760
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq164760
    | exact resolve eq164760 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164760
  have eq165155 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq165056
       have i₂ := eq154139 x
       grind)
    | exact superpose eq154139 eq165056
    | exact resolve eq165056 eq154139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165056
  have eq165156 : y = (M.op x x) := by grind
  clear eq165155
  have eq166152 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq20 x X0 x
       have i₂ := eq165156
       grind)
    | exact superpose eq165156 eq20
    | exact resolve eq20 eq165156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq166156 : ∀ X0 : G, (M.op x y) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq25 x X0 x
       have i₂ := eq165156
       grind)
    | exact superpose eq165156 eq25
    | exact resolve eq25 eq165156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq168407 : ∀ X1 : G, (M.op x y) = (M.op x (k x X1)) ∨ (M.op x x) = X1 := by
    intro X1
    first
    | (have i₁ := eq11909 x X1 x
       have i₂ := eq166152 x
       grind)
    | exact superpose eq166152 eq11909
    | (have j0 := eq11909 x X1 x
       grind)
    | exact resolve eq11909 eq166152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11909 eq166152
  have eq168620 : ∀ X1 : G, (M.op x y) = (M.op x (k x X1)) ∨ y = X1 := by
    intro X1
    first
    | (have i₁ := eq168407 X1
       have i₂ := eq165156
       grind)
    | exact superpose eq165156 eq168407
    | (have j0 := eq168407 X1
       grind)
    | exact resolve eq168407 eq165156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168407
  have eq172053 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq154139 X0
       have i₂ := eq153652 X0 X1
       grind)
    | (have i₁ := eq154139 X1
       have i₂ := eq153652 X1 X1
       grind)
    | exact superpose eq153652 eq154139
    | (have j1 := eq153652 X0 X1
       grind)
    | exact resolve eq154139 eq153652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172110 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq153652 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153652
  have eq172113 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq172110 X0 X1
       have i₂ := eq154139 X0
       grind)
    | exact superpose eq154139 eq172110
    | (have j0 := eq172110 X0 X1
       grind)
    | (have r₁ := eq172110 X0 X0
       have r₂ := eq154139 X0
       grind)
    | exact resolve eq172110 eq154139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172110
  have eq172236 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq172113 X0 X1
       have i₂ := eq154139 X0
       grind)
    | exact superpose eq154139 eq172113
    | (have j0 := eq172113 X0 X1
       grind)
    | exact resolve eq172113 eq154139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172113
  have eq172721 : ∀ X0 : G, (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (k x (k x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq172236 x (k x X0)
       have i₂ := eq168620 X0
       grind)
    | exact superpose eq168620 eq172236
    | (have j0 := eq172236 x y
       have j1 := eq168620 X0
       grind)
    | exact resolve eq172236 eq168620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168620
  have eq172814 : ∀ X0 : G, y ≠ (M.op x y) ∨ (M.op x x) = (k x (k x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq172721 X0
       have i₂ := eq165156
       grind)
    | exact superpose eq165156 eq172721
    | (have j0 := eq172721 X0
       grind)
    | exact resolve eq172721 eq165156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172721
  have eq172848 : ∀ X0 : G, y ≠ (M.op x y) ∨ y = (k x (k x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq172814 X0
       have i₂ := eq165156
       grind)
    | exact superpose eq165156 eq172814
    | (have j0 := eq172814 (k x (k x X0))
       grind)
    | exact resolve eq172814 eq165156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172814
  have eq175812 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 (σ X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq153855 X0 X1
       have i₂ := eq154139 X0
       grind)
    | exact superpose eq154139 eq153855
    | exact resolve eq153855 eq154139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153855
  have eq178962 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq175812 x X0
       have i₂ := eq165156
       grind)
    | exact superpose eq165156 eq175812
    | exact resolve eq175812 eq165156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175812
  have eq179510 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq8 (σ x) X0 x
       have i₂ := eq178962 x
       grind)
    | exact superpose eq178962 eq8
    | exact resolve eq8 eq178962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179542 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq101189 (σ x) x
       have i₂ := eq178962 x
       grind)
    | exact superpose eq178962 eq101189
    | exact resolve eq101189 eq178962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101189 eq178962
  have eq179791 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (k x X0))) ∨ (k x x) = X0 := by
    intro X0
    first
    | (have i₁ := eq179510 (σ X0)
       have i₂ := eq154065 x X0
       grind)
    | exact superpose eq154065 eq179510
    | (have j1 := eq154065 x X0
       grind)
    | exact resolve eq179510 eq154065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154065 eq179510
  have eq180069 : ∀ X0 : G, (M.op x x) = X0 ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (k x X0))) := by
    intro X0
    first
    | (have i₁ := eq179791 X0
       have i₂ := eq154139 x
       grind)
    | exact superpose eq154139 eq179791
    | (have j0 := eq179791 X0
       grind)
    | exact resolve eq179791 eq154139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179791
  have eq180105 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (k x X0))) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq180069 X0
       have i₂ := eq165156
       grind)
    | exact superpose eq165156 eq180069
    | (have j0 := eq180069 X0
       grind)
    | exact resolve eq180069 eq165156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180069
  have eq180183 : (τ (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq44 x (M.op (σ x) (σ y))
       have i₂ := eq179542
       grind)
    | exact superpose eq179542 eq44
    | exact resolve eq44 eq179542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq179542
  have eq206172 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x X0))) ∨ y = X0 ∨ (M.op x x) = X0 := by
    intro X0
    first
    | (have i₁ := eq180105 X0
       have i₂ := eq934 X0 x
       grind)
    | exact superpose eq934 eq180105
    | (have j0 := eq180105 X0
       have j1 := eq934 X0 x
       grind)
    | exact resolve eq180105 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934 eq180105
  have eq206301 : ∀ X0 : G, y = X0 ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x X0))) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq206172 X0
       have i₂ := eq165156
       grind)
    | exact superpose eq165156 eq206172
    | (have j0 := eq206172 X0
       grind)
    | exact resolve eq206172 eq165156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206172
  have eq206302 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x X0))) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq206301 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206301
  have eq211105 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq153199 X0 X1
       have i₂ := eq172053 X0 X1
       grind)
    | exact superpose eq172053 eq153199
    | (have j1 := eq172053 X0 X1
       grind)
    | exact resolve eq153199 eq172053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153199 eq172053
  have eq211295 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq211105 X0 X1
       have i₂ := eq154139 X0
       grind)
    | exact superpose eq154139 eq211105
    | (have j0 := eq211105 X0 X1
       grind)
    | exact resolve eq211105 eq154139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154139 eq211105
  have eq211340 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq211295 X0 X1
       have j1 := eq172236 X0 X1
       grind)
    | (have r₁ := eq211295 X0 X1
       have r₂ := eq172236 X0 X1
       grind)
    | (have r₁ := eq211295 X1 X1
       have r₂ := eq172236 X1 X1
       grind)
    | exact resolve eq211295 eq172236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172236 eq211295
  have eq225422 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op x (M.op x X0))) ∨ y = X0 ∨ (M.op x x) = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq206302 X0
       have i₂ := eq211340 x (M.op x X0)
       grind)
    | exact superpose eq211340 eq206302
    | (have j0 := eq206302 X0
       have j1 := eq211340 x (M.op x X0)
       grind)
    | exact resolve eq206302 eq211340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206302 eq211340
  have eq225654 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = X0 ∨ (M.op x x) = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq225422 X0
       have i₂ := eq166156 X0
       grind)
    | exact superpose eq166156 eq225422
    | (have j0 := eq225422 X0
       grind)
    | exact resolve eq225422 eq166156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225422
  have eq225688 : ∀ X0 : G, y = X0 ∨ (M.op x x) = (k x (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq225654 X0
       grind)
    | (have r₁ := eq225654 X0
       have r₂ := eq14
       grind)
    | exact resolve eq225654 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225654
  have eq225701 : ∀ X0 : G, y = (k x (M.op x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq225688 X0
       have i₂ := eq165156
       grind)
    | exact superpose eq165156 eq225688
    | (have j0 := eq225688 (k x (M.op x X0))
       grind)
    | exact resolve eq225688 eq165156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165156 eq225688
  have eq225911 : ∀ X0 : G, y = (M.op x (M.op x X0)) ∨ y = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq100924 x X0
       have i₂ := eq225701 (M.op x X0)
       grind)
    | exact superpose eq225701 eq100924
    | (have j1 := eq225701 (M.op x (M.op x X0))
       grind)
    | exact resolve eq100924 eq225701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100924 eq225701
  have eq225999 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq225911 X0
       have i₂ := eq166156 X0
       grind)
    | exact superpose eq166156 eq225911
    | (have j0 := eq225911 y
       grind)
    | exact resolve eq225911 eq166156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166156 eq225911
  have eq227459 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq225999 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225999
  have eq227460 : y = (M.op x y) := by grind
  clear eq227459
  have eq227560 : ∀ X0 : G, y ≠ y ∨ y = (k x (k x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq172848 X0
       have i₂ := eq227460
       grind)
    | exact superpose eq227460 eq172848
    | (have j0 := eq172848 X0
       grind)
    | (have r₁ := eq172848 X0
       have r₂ := eq227460
       grind)
    | exact resolve eq172848 eq227460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172848
  have eq227805 : ∀ X0 : G, y = (k x (k x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq227560 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227560
  have eq232043 : y = (k x (τ (M.op (σ x) (σ y)))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq227805 (τ (M.op (σ x) (σ y)))
       have i₂ := eq180183
       grind)
    | exact superpose eq180183 eq227805
    | (have j0 := eq227805 (k x (τ (M.op (σ x) (σ y))))
       grind)
    | exact resolve eq227805 eq180183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227805
  have eq232392 : y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq232043
       have i₂ := eq180183
       grind)
    | exact superpose eq180183 eq232043
    | exact resolve eq232043 eq180183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180183 eq232043
  have eq232393 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq232392
  have eq232536 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ y))
       have i₂ := eq232393
       grind)
    | exact superpose eq232393 eq10
    | exact resolve eq10 eq232393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232393
  have eq233361 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq232536
       grind)
    | exact superpose eq232536 eq14
    | exact resolve eq14 eq232536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232536
  have eq233687 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq233361
       have i₂ := eq227460
       grind)
    | exact superpose eq227460 eq233361
    | exact resolve eq233361 eq227460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227460 eq233361
  have eq233688 : False := by grind
  exact eq233688

/-- `Equation4297`: `x ◇ (x ◇ y) = y ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pyy_pxy_Equation4297 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law4297 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4297.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op X2 X2)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) (M.op X3 X3)) = (M.op X2 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X2 X0) X3
       have i₂ := eq8 X2 X0 X1
       grind)
    | (have i₁ := eq8 X1 (M.op X2 X2) X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op X1 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 (M.op X2 X2) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | (have i₁ := eq8 X0 (M.op X0 X1) X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 x X0 X3
       have i₂ := eq8 x X0 X1
       grind)
    | (have i₁ := eq8 x x x
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X2 X1 x
       grind)
    | (have i₁ := eq8 X0 X1 X1
       have i₂ := eq8 X1 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21
    | exact resolve eq21 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq60 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (M.op X1 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    grind
  have eq63 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X2 (k X0 (M.op X0 X0))) := by
    intro X0 X1 X2
    grind
  have eq65 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 (k (τ X0) X1) X2
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq34
    | exact resolve eq34 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op X3 (M.op (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X0 X0)
       have i₂ := eq24 (M.op X0 X0) X0 X1
       grind)
    | (have i₁ := eq8 X2 X3 (M.op X0 X0)
       have i₂ := eq24 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq24 eq8
    | exact resolve eq8 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = (M.op X2 (M.op X2 (M.op X3 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq28 X2 (M.op X3 X3) X1
       have i₂ := eq8 X0 X1 X3
       grind)
    | (have i₁ := eq28 X0 (M.op X0 X1) X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq28
    | exact resolve eq28 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq174 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = (k X2 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 X2 X1
       have i₂ := eq8 X0 X1 X2
       grind)
    | (have i₁ := eq60 X1 X1
       have i₂ := eq8 X1 X1 X2
       grind)
    | exact superpose eq8 eq60
    | exact resolve eq60 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (k X1 (σ (M.op (τ X1) (τ X1)))) = (σ (M.op X0 (M.op X0 (M.op (τ X1) (τ X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op (τ X1) (τ X1))
       have i₂ := eq60 (τ X1) X0
       grind)
    | exact superpose eq60 eq16
    | exact resolve eq16 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq228 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 (k X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 X0
       have i₂ := eq63 X1 X0 X0
       grind)
    | exact superpose eq63 eq60
    | exact resolve eq60 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq63
  have eq358 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq462 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op X1 (M.op X2 X2))) = (M.op X0 (M.op X1 (M.op X4 X4))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq22 X1 X4 X0 x
       have i₂ := eq22 X1 X2 X0 x
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq721 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op X3 (M.op X0 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op x x)
       have i₂ := eq23 X1 X0 x x
       grind)
    | exact superpose eq23 eq8
    | exact resolve eq8 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq1705 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq358 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq1781 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq1705 (σ X0)
       grind)
    | exact superpose eq1705 eq13
    | exact resolve eq13 eq1705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1783 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46 X0 X0
       have i₂ := eq1705 (τ X0)
       grind)
    | exact superpose eq1705 eq46
    | exact resolve eq46 eq1705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1790 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1783 X0
       have i₂ := eq1705 X0
       grind)
    | exact superpose eq1705 eq1783
    | exact resolve eq1783 eq1705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1783
  have eq1792 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1781 X0
       have i₂ := eq1705 X0
       grind)
    | exact superpose eq1705 eq1781
    | exact resolve eq1781 eq1705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1705 eq1781
  have eq1957 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 X1))) = (k (τ X0) (τ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq174 X2 X1 (τ X0)
       have i₂ := eq1790 X0
       grind)
    | exact superpose eq1790 eq174
    | exact resolve eq174 eq1790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1790
  have eq1982 : ∀ X0 X1 X2 : G, (τ (k X0 (M.op X0 X0))) = (M.op X1 (M.op X2 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1957 X0 X1 X2
       have i₂ := eq46 (M.op X0 X0) X0
       grind)
    | exact superpose eq46 eq1957
    | exact resolve eq1957 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957
  have eq2061 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq9
    | (have j1 := eq43 X0 X1
       grind)
    | exact resolve eq9 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq2133 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2061 X0 X1
       have i₂ := eq1792 X0
       grind)
    | exact superpose eq1792 eq2061
    | (have j0 := eq2061 X0 X1
       grind)
    | exact resolve eq2061 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2061
  have eq2202 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2133 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq2133
    | (have j0 := eq2133 X0 X1
       grind)
    | exact resolve eq2133 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2133
  have eq2269 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X2 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 (σ X0)
       have i₂ := eq1792 X0
       grind)
    | exact superpose eq1792 eq8
    | exact resolve eq8 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2277 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 X2 (σ X0)
       have i₂ := eq1792 X0
       grind)
    | exact superpose eq1792 eq24
    | exact resolve eq24 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3962 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (σ (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2277 (σ X0) X1 X2
       have i₂ := eq1792 X0
       grind)
    | exact superpose eq1792 eq2277
    | exact resolve eq2277 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1792
  have eq14827 : ∀ X0 X1 : G, (M.op (k X1 (M.op X1 X1)) X0) = (k (k X1 (M.op X1 X1)) X0) ∨ (M.op (k X1 (M.op X1 X1)) X0) = (k (k X1 (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq228 (k X1 (M.op X1 X1)) X1
       have i₂ := eq12 (k X1 (M.op X1 X1)) X1
       grind)
    | (have i₁ := eq228 X0 X1
       have i₂ := eq12 X0 (M.op X0 (k X1 (M.op X1 X1)))
       grind)
    | exact superpose eq12 eq228
    | (have j1 := eq12 (k X1 (M.op X1 X1)) X0
       grind)
    | exact resolve eq228 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq14931 : ∀ X0 X1 : G, (M.op (k X1 (M.op X1 X1)) X0) = (k (k X1 (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq14827 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14827
  have eq26928 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2202 x y
       grind)
    | exact superpose eq2202 eq14
    | (have j1 := eq2202 x y
       grind)
    | exact resolve eq14 eq2202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2202
  have eq27429 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq26928
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq26928
    | (have j1 := eq12 x y
       grind)
    | exact resolve eq26928 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26928
  have eq27435 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq27429
  have eq27436 : y = (M.op x x) := by grind
  clear eq27435
  have eq27673 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq8
    | exact resolve eq8 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27679 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1 x
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq24
    | exact resolve eq24 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq27699 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op (M.op X2 X2) y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq111 X2 x X0 X1
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq111
    | exact resolve eq111 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq27722 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 X2))) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq462 X0 X1 X2 x
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq462
    | exact resolve eq462 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq27752 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq2269 x X0 X1
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq2269
    | exact resolve eq2269 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269
  have eq27753 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq2277 x X0 X1
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq2277
    | exact resolve eq2277 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2277
  have eq27779 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq144 x x X0 X1
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq144
    | exact resolve eq144 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq27781 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq174 x x X0
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq174
    | exact resolve eq174 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq27786 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op x (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq721 x x X0 X1
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq721
    | exact resolve eq721 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq27788 : ∀ X0 : G, (τ (k X0 (M.op X0 X0))) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1982 X0 x x
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq1982
    | exact resolve eq1982 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1982 eq27436
  have eq27833 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X0 (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq27722 X0 X1 x
       have i₂ := eq27753 X1 x
       grind)
    | exact superpose eq27753 eq27722
    | exact resolve eq27722 eq27753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27722
  have eq27850 : ∀ X1 X2 : G, (M.op X1 (M.op (M.op X2 X2) y)) = (M.op X1 (σ y)) := by
    intro X1 X2
    first
    | (have i₁ := eq27699 x X1 X2
       have i₂ := eq27752 x X1
       grind)
    | exact superpose eq27752 eq27699
    | exact resolve eq27699 eq27752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27699
  have eq35877 : ∀ X0 X1 : G, (M.op X0 (σ (σ (M.op X1 X1)))) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq3962 X1 X0 X0
       have i₂ := eq27673 X0 X0
       grind)
    | exact superpose eq27673 eq3962
    | exact resolve eq3962 eq27673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52167 : ∀ X0 X1 X2 : G, (M.op X1 (σ (σ (M.op X2 X2)))) = (M.op X1 (M.op (M.op X0 X0) y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3962 X2 X1 (M.op X0 X0)
       have i₂ := eq27679 (M.op X0 X0) X0
       grind)
    | exact superpose eq27679 eq3962
    | exact resolve eq3962 eq27679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3962 eq27679
  have eq52290 : ∀ X1 X2 : G, (M.op X1 (σ (σ (M.op X2 X2)))) = (M.op X1 (σ y)) := by
    intro X1 X2
    first
    | (have i₁ := eq52167 x X1 X2
       have i₂ := eq27850 X1 x
       grind)
    | exact superpose eq27850 eq52167
    | exact resolve eq52167 eq27850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27850 eq52167
  have eq52670 : ∀ X1 : G, (M.op X1 y) = (M.op X1 (σ y)) := by
    intro X1
    first
    | (have i₁ := eq52290 X1 x
       have i₂ := eq35877 X1 x
       grind)
    | exact superpose eq35877 eq52290
    | exact resolve eq52290 eq35877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35877 eq52290
  have eq56146 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq52670 (σ x)
       grind)
    | exact superpose eq52670 eq14
    | exact resolve eq14 eq52670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134979 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X1 (M.op (τ X0) (τ X0)))) (τ X2)) = (τ (k (k X0 (σ (M.op (τ X0) (τ X0)))) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 (M.op X1 (M.op X1 (M.op (τ X0) (τ X0)))) X2
       have i₂ := eq185 X1 X0
       grind)
    | exact superpose eq185 eq34
    | exact resolve eq34 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq185
  have eq134998 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X1 (M.op (τ X0) (τ X0)))) (τ X2)) = (k (k (τ X0) (M.op (τ X0) (τ X0))) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq134979 X0 X1 X2
       have i₂ := eq65 X0 (M.op (τ X0) (τ X0)) X2
       grind)
    | exact superpose eq65 eq134979
    | exact resolve eq134979 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq134979
  have eq135201 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X1 (M.op (τ X0) (τ X0)))) (τ X2)) = (M.op (k (τ X0) (M.op (τ X0) (τ X0))) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq134998 X0 X1 X2
       have i₂ := eq14931 (τ X2) (τ X0)
       grind)
    | exact superpose eq14931 eq134998
    | exact resolve eq134998 eq14931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134998
  have eq135395 : ∀ X0 X1 X2 : G, (M.op (M.op x (M.op x y)) (τ X2)) = (k (M.op X1 (M.op X1 (M.op (τ X0) (τ X0)))) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq135201 X0 X1 X2
       have i₂ := eq27781 (τ X0)
       grind)
    | exact superpose eq27781 eq135201
    | exact resolve eq135201 eq27781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135201
  have eq135579 : ∀ X2 : G, (M.op (M.op x (M.op x y)) (τ X2)) = (k (M.op x (M.op x y)) (τ X2)) := by
    intro X2
    first
    | (have i₁ := eq135395 x x X2
       have i₂ := eq27779 x (τ x)
       grind)
    | exact superpose eq27779 eq135395
    | exact resolve eq135395 eq27779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27779 eq135395
  have eq135740 : ∀ X2 : G, (M.op (M.op y (σ y)) (τ X2)) = (k (M.op y (σ y)) (τ X2)) := by
    intro X2
    first
    | (have i₁ := eq135579 X2
       have i₂ := eq27752 x y
       grind)
    | exact superpose eq27752 eq135579
    | exact resolve eq135579 eq27752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135579
  have eq135891 : ∀ X2 : G, (M.op (M.op y y) (τ X2)) = (k (M.op y y) (τ X2)) := by
    intro X2
    first
    | (have i₁ := eq135740 X2
       have i₂ := eq52670 y
       grind)
    | exact superpose eq52670 eq135740
    | exact resolve eq135740 eq52670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135740
  have eq340913 : ∀ X0 X1 : G, (τ (k (k X0 (M.op X0 X0)) X1)) = (k (M.op x (M.op x y)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X1 (k X0 (M.op X0 X0))
       have i₂ := eq27788 X0
       grind)
    | exact superpose eq27788 eq46
    | exact resolve eq46 eq27788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq27788
  have eq340915 : ∀ X0 X1 : G, (τ (k (k X0 (M.op X0 X0)) X1)) = (k (M.op y (σ y)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq340913 X0 X1
       have i₂ := eq27752 x y
       grind)
    | exact superpose eq27752 eq340913
    | exact resolve eq340913 eq27752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340913
  have eq340990 : ∀ X0 X1 : G, (k (M.op y y) (τ X1)) = (τ (k (k X0 (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq340915 X0 X1
       have i₂ := eq52670 y
       grind)
    | exact superpose eq52670 eq340915
    | exact resolve eq340915 eq52670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340915
  have eq341065 : ∀ X0 X1 : G, (k (M.op y y) (τ X1)) = (τ (M.op (k X0 (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq340990 X0 X1
       have i₂ := eq14931 X1 X0
       grind)
    | exact superpose eq14931 eq340990
    | exact resolve eq340990 eq14931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14931 eq340990
  have eq341136 : ∀ X1 : G, (k (M.op y y) (τ X1)) = (τ (M.op (M.op x (M.op x y)) X1)) := by
    intro X1
    first
    | (have i₁ := eq341065 x X1
       have i₂ := eq27781 x
       grind)
    | exact superpose eq27781 eq341065
    | exact resolve eq341065 eq27781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27781 eq341065
  have eq341187 : ∀ X1 : G, (k (M.op y y) (τ X1)) = (τ (M.op (M.op y (σ y)) X1)) := by
    intro X1
    first
    | (have i₁ := eq341136 X1
       have i₂ := eq27752 x y
       grind)
    | exact superpose eq27752 eq341136
    | exact resolve eq341136 eq27752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341136
  have eq341228 : ∀ X1 : G, (k (M.op y y) (τ X1)) = (τ (M.op (M.op y y) X1)) := by
    intro X1
    first
    | (have i₁ := eq341187 X1
       have i₂ := eq52670 y
       grind)
    | exact superpose eq52670 eq341187
    | exact resolve eq341187 eq52670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341187
  have eq341257 : ∀ X1 : G, (M.op (M.op y y) (τ X1)) = (τ (M.op (M.op y y) X1)) := by
    intro X1
    first
    | (have i₁ := eq341228 X1
       have i₂ := eq135891 X1
       grind)
    | exact superpose eq135891 eq341228
    | exact resolve eq341228 eq135891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135891 eq341228
  have eq563820 : ∀ X0 : G, (τ (M.op X0 y)) = (M.op (M.op y y) (τ (M.op (M.op y y) X0))) := by
    intro X0
    first
    | (have i₁ := eq341257 (M.op (M.op y y) X0)
       have i₂ := eq27673 (M.op y y) X0
       grind)
    | exact superpose eq27673 eq341257
    | exact resolve eq341257 eq27673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27673
  have eq563944 : ∀ X0 : G, (τ (M.op X0 y)) = (M.op (M.op y y) (M.op (M.op y y) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq563820 X0
       have i₂ := eq341257 X0
       grind)
    | exact superpose eq341257 eq563820
    | exact resolve eq563820 eq341257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341257 eq563820
  have eq564013 : ∀ X0 : G, (M.op (τ X0) (M.op x (M.op x y))) = (τ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq563944 X0
       have i₂ := eq27786 (M.op y y) (τ X0)
       grind)
    | exact superpose eq27786 eq563944
    | exact resolve eq563944 eq27786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27786 eq563944
  have eq564072 : ∀ X0 : G, (M.op (τ X0) (M.op y (σ y))) = (τ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq564013 X0
       have i₂ := eq27752 x y
       grind)
    | exact superpose eq27752 eq564013
    | exact resolve eq564013 eq27752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27752 eq564013
  have eq564123 : ∀ X0 : G, (M.op (τ X0) (M.op y y)) = (τ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq564072 X0
       have i₂ := eq27833 (τ X0) y
       grind)
    | exact superpose eq27833 eq564072
    | exact resolve eq564072 eq27833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27833 eq564072
  have eq564165 : ∀ X0 : G, (M.op (τ X0) (σ y)) = (τ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq564123 X0
       have i₂ := eq27753 (τ X0) y
       grind)
    | exact superpose eq27753 eq564123
    | exact resolve eq564123 eq27753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27753 eq564123
  have eq564186 : ∀ X0 : G, (M.op (τ X0) y) = (τ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq564165 X0
       have i₂ := eq52670 (τ X0)
       grind)
    | exact superpose eq52670 eq564165
    | exact resolve eq564165 eq52670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52670 eq564165
  have eq567288 : ∀ X0 : G, (M.op X0 y) = (σ (M.op (τ X0) y)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 y)
       have i₂ := eq564186 X0
       grind)
    | exact superpose eq564186 eq10
    | exact resolve eq10 eq564186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564186
  have eq569280 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq567288 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq567288
    | exact resolve eq567288 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567288
  have eq570319 : (M.op (σ x) y) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq56146
       have i₂ := eq569280 x
       grind)
    | exact superpose eq569280 eq56146
    | (have r₁ := eq56146
       have r₂ := eq569280 x
       grind)
    | exact resolve eq56146 eq569280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56146 eq569280
  have eq570329 : False := by grind
  exact eq570329

/-- `Equation430`: `x = x ◇ (y ◇ (x ◇ (y ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation430 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law430 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X1 X1)))) = X0 := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 (M.op X0 X0)
       have i₂ := eq8 (M.op X0 X0) X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq18 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq26 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq24
    | exact resolve eq24 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq26 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq26
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq26 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq26 x y
       grind)
    | exact superpose eq26 eq14
    | (have j1 := eq26 x y
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq26 X0 X1
       grind)
    | exact superpose eq26 eq9
    | (have j1 := eq26 X0 X1
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (σ X1)
       have i₂ := eq26 X1 X0
       grind)
    | exact superpose eq26 eq18
    | (have j1 := eq26 X1 X0
       grind)
    | exact resolve eq18 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq447 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq504 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq447 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq447
    | (have j0 := eq447 X0 X1
       grind)
    | exact resolve eq447 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq554 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq555 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1
       have i₂ := eq504 X0 X1
       grind)
    | (have i₁ := eq18 X0
       have i₂ := eq504 (M.op X0 X0) X1
       grind)
    | exact superpose eq504 eq18
    | (have j1 := eq504 X0 X1
       grind)
    | exact resolve eq18 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq841 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq18 (σ X0)
       have i₂ := eq51 X0 X0
       grind)
    | exact superpose eq51 eq18
    | (have j1 := eq51 X0 X0
       grind)
    | exact resolve eq18 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1042 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq146
       have i₂ := eq555 y x
       grind)
    | exact superpose eq555 eq146
    | (have j1 := eq555 y x
       grind)
    | (have r₁ := eq146
       have r₂ := eq555 y x
       grind)
    | exact resolve eq146 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq1043 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq146
       have i₂ := eq554 y x
       grind)
    | exact superpose eq554 eq146
    | (have j1 := eq554 y x
       grind)
    | (have r₁ := eq146
       have r₂ := eq554 y x
       grind)
    | exact resolve eq146 eq554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq1044 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq146
       have i₂ := eq504 y x
       grind)
    | exact superpose eq504 eq146
    | (have j1 := eq504 (σ y) (σ x)
       grind)
    | (have r₁ := eq146
       have r₂ := eq504 y x
       grind)
    | exact resolve eq146 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq504
  have eq1045 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1044
  have eq1046 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by grind
  clear eq1043
  have eq1047 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1042
  have eq1062 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  have eq1063 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18 (σ x)
       have i₂ := eq1045
       grind)
    | exact superpose eq1045 eq18
    | exact resolve eq18 eq1045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq1070 : (σ y) = (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1062
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq1062
    | exact resolve eq1062 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq1101 : (k x y) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq1070
       grind)
    | exact superpose eq1070 eq9
    | exact resolve eq9 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070
  have eq1138 : y = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1101
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1101
    | exact resolve eq1101 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101
  have eq1189 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1138
       grind)
    | exact superpose eq1138 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq1138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138
  have eq1196 : y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq1189
  have eq1324 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq162 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq1354 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq134 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq134
    | (have j0 := eq134 X1 (τ X0)
       grind)
    | exact resolve eq134 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq1448 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1354 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1354
    | (have j0 := eq1354 X0 X1
       grind)
    | exact resolve eq1354 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1354
  have eq1456 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1448 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1448
    | (have j0 := eq1448 X0 X1
       grind)
    | exact resolve eq1448 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448
  have eq1602 : (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) := by grind
  clear eq1046
  have eq1611 : (σ y) = (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1602
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq1602
    | exact resolve eq1602 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1602
  have eq1743 : (k x y) = (τ (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq1611
       grind)
    | exact superpose eq1611 eq9
    | exact resolve eq9 eq1611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1611
  have eq1786 : y = (k x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1743
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1743
    | exact resolve eq1743 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743
  have eq1787 : y = (k x y) := by grind
  clear eq1786
  have eq1824 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22 y x
       have i₂ := eq1787
       grind)
    | exact superpose eq1787 eq22
    | (have j0 := eq22 y x
       grind)
    | exact resolve eq22 eq1787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1899 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq1824
  have eq2308 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq153 x x
       have i₂ := eq1047
       grind)
    | exact superpose eq1047 eq153
    | exact resolve eq153 eq1047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq1047
  have eq2334 : x = y ∨ (σ y) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2308
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2308
    | exact resolve eq2308 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2308
  have eq2335 : (σ y) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2334
       have r₂ := eq1899
       grind)
    | exact resolve eq2334 eq1899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2334
  have eq2488 : (k x x) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq2335
       grind)
    | exact superpose eq2335 eq9
    | exact resolve eq9 eq2335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2335
  have eq2532 : y = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2488
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2488
    | exact resolve eq2488 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2488
  have eq2815 : y = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24 x x
       have i₂ := eq2532
       grind)
    | exact superpose eq2532 eq24
    | exact resolve eq24 eq2532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2532
  have eq2825 : x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq2815
       have r₂ := eq1899
       grind)
    | exact resolve eq2815 eq1899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2815
  have eq3017 : x = y ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1196
       have i₂ := eq2825
       grind)
    | exact superpose eq2825 eq1196
    | exact resolve eq1196 eq2825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196 eq2825
  have eq3026 : y = (M.op x x) ∨ x = y := by grind
  clear eq3017
  have eq3274 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18 x
       have i₂ := eq3026
       grind)
    | exact superpose eq3026 eq18
    | exact resolve eq18 eq3026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3026
  have eq3287 : x = (M.op x y) := by
    first
    | (have r₁ := eq3274
       have r₂ := eq1899
       grind)
    | exact resolve eq3274 eq1899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1899 eq3274
  have eq5143 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1063
       grind)
    | exact superpose eq1063 eq14
    | exact resolve eq14 eq1063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063
  have eq5158 : (σ x) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5143
       have i₂ := eq3287
       grind)
    | exact superpose eq3287 eq5143
    | exact resolve eq5143 eq3287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5143
  have eq5159 : y = (M.op x x) := by grind
  clear eq5158
  have eq12751 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1324 x y
       have i₂ := eq1787
       grind)
    | exact superpose eq1787 eq1324
    | (have j0 := eq1324 x y
       grind)
    | exact resolve eq1324 eq1787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324
  have eq12952 : y = (M.op x y) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq1787
       have i₂ := eq1456 x y
       grind)
    | exact superpose eq1456 eq1787
    | (have j1 := eq1456 x y
       grind)
    | exact resolve eq1787 eq1456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1456 eq1787
  have eq13072 : x = y ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq12952
       have i₂ := eq3287
       grind)
    | exact superpose eq3287 eq12952
    | exact resolve eq12952 eq3287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12952
  have eq13073 : y = (k x x) ∨ x = y := by grind
  clear eq13072
  have eq17730 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq841 x
       have i₂ := eq13073
       grind)
    | exact superpose eq13073 eq841
    | exact resolve eq841 eq13073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841 eq13073
  have eq17822 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq17730
       have r₂ := eq12751
       grind)
    | exact resolve eq17730 eq12751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17730
  have eq17875 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq17822
       grind)
    | exact superpose eq17822 eq14
    | exact resolve eq14 eq17822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17822
  have eq17920 : (σ x) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq17875
       have i₂ := eq3287
       grind)
    | exact superpose eq3287 eq17875
    | exact resolve eq17875 eq3287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3287 eq17875
  have eq17921 : x = y := by grind
  clear eq17920
  have eq17977 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq17921
       grind)
    | exact superpose eq17921 eq14
    | exact resolve eq14 eq17921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18005 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq12751
       have i₂ := eq17921
       grind)
    | exact superpose eq17921 eq12751
    | exact resolve eq12751 eq17921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12751
  have eq18008 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq18005
  have eq18016 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq17977
       have i₂ := eq5159
       grind)
    | exact superpose eq5159 eq17977
    | exact resolve eq17977 eq5159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5159 eq17977
  have eq18018 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq18016
       have i₂ := eq18008
       grind)
    | exact superpose eq18008 eq18016
    | exact resolve eq18016 eq18008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18008 eq18016
  have eq18021 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq18018
       have i₂ := eq17921
       grind)
    | exact superpose eq17921 eq18018
    | exact resolve eq18018 eq17921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17921 eq18018
  have eq18022 : False := by grind
  exact eq18022

/-- `Equation430`: `x = x ◇ (y ◇ (x ◇ (y ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pyx_pxy_Equation430 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law430 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X1 X1)))) = X0 := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 (M.op X0 X0)
       have i₂ := eq8 (M.op X0 X0) X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq39 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq35 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq166 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq39 x y
       grind)
    | exact superpose eq39 eq14
    | (have j1 := eq39 x y
       grind)
    | exact resolve eq14 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq202 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq62 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq243 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq202 (σ X0)
       grind)
    | exact superpose eq202 eq13
    | exact resolve eq13 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq243 X0
       have i₂ := eq202 X0
       grind)
    | exact superpose eq202 eq243
    | exact resolve eq243 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq243
  have eq369 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0)
       have i₂ := eq254 X0
       grind)
    | exact superpose eq254 eq22
    | exact resolve eq22 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1077 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq166
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq166
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq166 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq1078 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1077
  have eq1082 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1078
       have i₂ := eq254 x
       grind)
    | exact superpose eq254 eq1078
    | exact resolve eq1078 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254 eq1078
  have eq1090 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq1082
       grind)
    | exact superpose eq1082 eq9
    | exact resolve eq9 eq1082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082
  have eq1126 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1090
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1090
    | exact resolve eq1090 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq1127 : y = (M.op x x) := by grind
  clear eq1126
  have eq1280 : x = (M.op x y) := by
    first
    | (have i₁ := eq22 x
       have i₂ := eq1127
       grind)
    | exact superpose eq1127 eq22
    | exact resolve eq22 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1284 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq369 x
       have i₂ := eq1127
       grind)
    | exact superpose eq1127 eq369
    | exact resolve eq369 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq1127
  have eq1707 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1284
       grind)
    | exact superpose eq1284 eq14
    | exact resolve eq14 eq1284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284
  have eq1713 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1707
       have i₂ := eq1280
       grind)
    | exact superpose eq1280 eq1707
    | exact resolve eq1707 eq1280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280 eq1707
  have eq1714 : False := by grind
  exact eq1714

/-- `Equation4301`: `x ◇ (x ◇ y) = z ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation4301 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4301 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4301.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X0 X2)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X3)) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X0 X2) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | (have i₁ := eq8 X0 (M.op X0 X1) X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X1 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 x X3
       have i₂ := eq8 X1 x X0
       grind)
    | (have i₁ := eq8 X0 X0 x
       have i₂ := eq8 X0 X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X1 X3) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 (M.op X1 X3)
       have i₂ := eq8 X1 X3 X0
       grind)
    | (have i₁ := eq8 X2 X1 (M.op X0 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 X2) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X0 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | (have i₁ := eq8 X0 X1 (M.op X0 X1)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X0 X2 x
       grind)
    | (have i₁ := eq8 X1 X1 X1
       have i₂ := eq8 X1 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq35 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 (M.op X1 X2)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X1 X2
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq72 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X3)) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X1 X2) X3
       have i₂ := eq20 X2 X1 X0
       grind)
    | (have i₁ := eq8 X2 (M.op X1 X2) X3
       have i₂ := eq20 X0 X1 X2
       grind)
    | exact superpose eq20 eq8
    | exact resolve eq8 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30
    | exact resolve eq30 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq99 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X2 X3 (M.op X1 X2)
       have i₂ := eq20 X2 X1 X0
       grind)
    | (have i₁ := eq25 X2 X3 (M.op X1 X2)
       have i₂ := eq20 X0 X1 X2
       grind)
    | exact superpose eq20 eq25
    | exact resolve eq25 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X0 X1))) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X2 X3 (M.op X0 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | (have i₁ := eq25 X0 X1 (M.op X0 X1)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq25
    | exact resolve eq25 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq128 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq44
  have eq138 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq33
    | exact resolve eq33 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq33 X1 (τ X0)
       grind)
    | exact superpose eq33 eq16
    | (have j1 := eq33 X1 (τ X0)
       grind)
    | exact resolve eq16 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq145 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq33 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq259 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X1)) = (M.op X2 (M.op X3 X0)) ∨ (M.op X3 X0) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X3 X3 X2 X1
       have i₂ := eq12 X3 X0
       grind)
    | (have i₁ := eq19 X0 X1 X2 X3
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 (M.op X2 X0)
       have i₂ := eq22 X0 X2 X3 X0
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq549 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X3 (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq19 X3 X4 X2 (M.op X0 X2)
       have i₂ := eq22 X2 X0 X1 X2
       grind)
    | exact superpose eq22 eq19
    | exact resolve eq19 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq551 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 X2 X3 (M.op X0 X3)
       have i₂ := eq22 X3 X0 X1 X3
       grind)
    | exact superpose eq22 eq20
    | exact resolve eq20 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq553 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X3 (M.op X4 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq72 X3 X4 X2 (M.op X0 X2)
       have i₂ := eq22 X2 X0 X1 X2
       grind)
    | exact superpose eq22 eq72
    | exact resolve eq72 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq865 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X2)) = (M.op (M.op X3 (M.op X3 X4)) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20 X2 (M.op X3 X0) (M.op X3 (M.op X3 X4))
       have i₂ := eq23 X3 X4 X0 X1
       grind)
    | exact superpose eq23 eq20
    | exact resolve eq20 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq23
  have eq974 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X3 (M.op X4 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq72 X3 X4 X2 X2
       have i₂ := eq551 X2 X2 X0 X1
       grind)
    | (have i₁ := eq72 X0 X1 X3 X2
       have i₂ := eq551 X0 X1 X2 X3
       grind)
    | exact superpose eq551 eq72
    | exact resolve eq72 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq977 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq72 X1 x X1 X0
       have i₂ := eq551 X1 (M.op x X1) X2 X3
       grind)
    | (have i₁ := eq72 X3 X1 (M.op X1 X3) X3
       have i₂ := eq551 X0 X1 (M.op X1 X3) X3
       grind)
    | exact superpose eq551 eq72
    | exact resolve eq72 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1492 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = X2 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq35 X1 X1 X0
       grind)
    | exact superpose eq35 eq12
    | (have j0 := eq12 X1 (k X1 X1)
       have j1 := eq35 X2 X1 X2
       grind)
    | exact resolve eq12 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1606 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op X2 (M.op (σ X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq35 (σ X1) (σ X0) X2
       grind)
    | exact superpose eq35 eq13
    | (have j1 := eq35 (σ X1) (σ X0) X2
       grind)
    | exact resolve eq13 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1856 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X2 (M.op X3 X2)) ∨ (M.op X2 (M.op X3 X2)) = (k X0 (M.op X2 (M.op X3 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq145 X0 (M.op X2 (M.op X3 X2))
       have i₂ := eq99 X2 X3 X0 X1
       grind)
    | (have i₁ := eq145 X2 (M.op X2 X3)
       have i₂ := eq99 X0 X1 X2 X3
       grind)
    | exact superpose eq99 eq145
    | (have j0 := eq145 X0 (M.op X2 (M.op X3 X2))
       grind)
    | (have r₁ := eq145 X2 (M.op X2 (M.op X0 (M.op X1 X0)))
       have r₂ := eq99 X0 X1 X2 (M.op X0 (M.op X1 X0))
       grind)
    | (have r₁ := eq145 X3 (M.op X3 (M.op X3 X3))
       have r₂ := eq99 X3 X3 X3 X3
       grind)
    | exact resolve eq145 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq1865 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (k X0 (M.op X2 (M.op X3 X2))) := by
    intro X0 X2 X3
    first
    | (have j0 := eq1856 X0 x X2 X3
       grind)
    | (have r₁ := eq1856 X0 x X2 X3
       have r₂ := eq551 X0 x X2 X3
       grind)
    | (have r₁ := eq1856 X3 X3 x x
       have r₂ := eq551 x x X3 X3
       grind)
    | exact resolve eq1856 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1856
  have eq2092 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X2 (M.op X2 X3)) ∨ (M.op X2 (M.op X2 X3)) = (k X0 (M.op X2 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq145 X0 (M.op X2 (M.op X2 X3))
       have i₂ := eq100 X2 X3 X0 X1
       grind)
    | (have i₁ := eq145 X2 (M.op X2 X3)
       have i₂ := eq100 X0 X1 X2 X3
       grind)
    | exact superpose eq100 eq145
    | (have j0 := eq145 X0 (M.op X2 (M.op X2 X3))
       grind)
    | (have r₁ := eq145 X2 (M.op X2 (M.op X2 X3))
       have r₂ := eq100 X2 X3 X2 X3
       grind)
    | (have r₁ := eq145 X2 (M.op X2 (M.op X0 (M.op X0 X1)))
       have r₂ := eq100 X0 X1 X2 (M.op X0 (M.op X0 X1))
       grind)
    | exact resolve eq145 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq2163 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (k X0 (M.op X2 (M.op X2 X3))) := by
    intro X0 X2 X3
    first
    | (have j0 := eq2092 X0 x X2 X3
       grind)
    | (have r₁ := eq2092 X0 x X2 X3
       have r₂ := eq546 X0 x X2 X3
       grind)
    | (have r₁ := eq2092 X2 X3 X0 x
       have r₂ := eq546 X0 x X2 X3
       grind)
    | exact resolve eq2092 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2092
  have eq2188 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq36 x y
       grind)
    | exact superpose eq36 eq14
    | (have j1 := eq36 x y
       grind)
    | exact resolve eq14 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2266 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq36 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq3108 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op X3 (M.op X4 (M.op X5 X4))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq72 X4 X5 X3 X3
       have i₂ := eq549 X3 X3 X0 X1 X2
       grind)
    | (have i₁ := eq72 X0 X1 X3 (M.op X3 X4)
       have i₂ := eq549 X0 X1 (M.op X3 X4) X3 X4
       grind)
    | exact superpose eq549 eq72
    | exact resolve eq72 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq549
  have eq6696 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (k X3 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1865 X0 X1 X3
       have i₂ := eq35 (M.op X3 X1) X1 x
       grind)
    | (have i₁ := eq1865 X0 x X1
       have i₂ := eq35 X0 X1 x
       grind)
    | exact superpose eq35 eq1865
    | (have j1 := eq35 X1 X0 x
       grind)
    | exact resolve eq1865 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1865
  have eq16314 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq39
    | exact resolve eq39 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq16478 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16314 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq16314
    | (have j0 := eq16314 X0 X1
       grind)
    | exact resolve eq16314 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16314
  have eq16502 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq144 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq144
    | exact resolve eq144 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq16611 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16502 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq16502
    | (have j0 := eq16502 X0 X1
       grind)
    | exact resolve eq16502 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16502
  have eq17220 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq546 X2 X3 (σ X0) (σ X1)
       have i₂ := eq138 X0 X1
       grind)
    | exact superpose eq138 eq546
    | (have j1 := eq138 X0 X1
       grind)
    | exact resolve eq546 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq77390 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq2188
       have i₂ := eq16611 x y
       grind)
    | exact superpose eq16611 eq2188
    | (have j1 := eq16611 x y
       grind)
    | (have r₁ := eq2188
       have r₂ := eq16611 x y
       grind)
    | exact resolve eq2188 eq16611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16611
  have eq77391 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2188
       have i₂ := eq16478 y x
       grind)
    | exact superpose eq16478 eq2188
    | (have j1 := eq16478 (σ y) (σ x)
       grind)
    | (have r₁ := eq2188
       have r₂ := eq16478 y x
       grind)
    | exact resolve eq2188 eq16478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2188 eq16478
  have eq77392 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq77391
  have eq77393 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by grind
  clear eq77390
  have eq77404 : (τ (σ y)) = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq128 x
       have i₂ := eq77392
       grind)
    | exact superpose eq77392 eq128
    | exact resolve eq128 eq77392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77572 : y = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq77404
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq77404
    | exact resolve eq77404 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77404
  have eq79070 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq77572
       grind)
    | exact superpose eq77572 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq77572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77572
  have eq79075 : y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq79070
  have eq80925 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x y) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq546 X0 X1 x y
       have i₂ := eq79075
       grind)
    | exact superpose eq79075 eq546
    | exact resolve eq546 eq79075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80927 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 X0)) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq551 x y X0 X1
       have i₂ := eq79075
       grind)
    | exact superpose eq79075 eq551
    | exact resolve eq551 eq79075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84923 : (τ (σ y)) = (k x (τ (σ y))) ∨ y = (k x y) := by
    first
    | (have i₁ := eq128 x
       have i₂ := eq77393
       grind)
    | exact superpose eq77393 eq128
    | exact resolve eq128 eq77393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq77393
  have eq85098 : y = (k x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq84923
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq84923
    | exact resolve eq84923 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84923
  have eq85099 : y = (k x y) := by grind
  clear eq85098
  have eq93634 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq80925 X0 (M.op X0 x)
       have i₂ := eq80925 X0 x
       grind)
    | exact superpose eq80925 eq80925
    | exact resolve eq80925 eq80925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93792 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq80925 (σ x) (σ x)
       have i₂ := eq77392
       grind)
    | exact superpose eq77392 eq80925
    | exact resolve eq80925 eq77392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77392 eq80925
  have eq94468 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq93792
  have eq94469 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq93634 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93634
  have eq96907 : y = (M.op y y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq80927 y x
       have i₂ := eq79075
       grind)
    | exact superpose eq79075 eq80927
    | exact resolve eq80927 eq79075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80927
  have eq97597 : y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq96907
  have eq100122 : y ≠ y ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq145 y y
       have i₂ := eq97597
       grind)
    | exact superpose eq97597 eq145
    | (have j0 := eq145 y y
       grind)
    | (have r₁ := eq145 y y
       have r₂ := eq97597
       grind)
    | exact resolve eq145 eq97597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq97597
  have eq100258 : y = (k y y) ∨ y = (M.op x x) := by grind
  clear eq100122
  have eq102835 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2266 y
       have i₂ := eq100258
       grind)
    | exact superpose eq100258 eq2266
    | (have j0 := eq2266 y
       grind)
    | exact resolve eq2266 eq100258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100258
  have eq102841 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq102835
  have eq142121 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq94468
       grind)
    | exact superpose eq94468 eq14
    | exact resolve eq14 eq94468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94468
  have eq145037 : y ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq142121
       have i₂ := eq79075
       grind)
    | exact superpose eq79075 eq142121
    | exact resolve eq142121 eq79075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142121
  have eq145040 : y ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq145037
  have eq153518 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq94469 X0
       have i₂ := eq79075
       grind)
    | exact superpose eq79075 eq94469
    | exact resolve eq94469 eq79075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79075 eq94469
  have eq153983 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq153518 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153518
  have eq157155 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 y) ∨ y = (M.op x x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq546 X0 X1 X2 y
       have i₂ := eq153983 X2
       grind)
    | exact superpose eq153983 eq546
    | exact resolve eq546 eq153983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq196046 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = y ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq153983 x
       have i₂ := eq157155 X0 X1 x
       grind)
    | exact superpose eq157155 eq153983
    | exact resolve eq153983 eq157155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153983 eq157155
  have eq196361 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = y ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have j0 := eq196046 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196046
  have eq200074 : y = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq196361 (σ y) (σ y)
       have i₂ := eq102841
       grind)
    | exact superpose eq102841 eq196361
    | exact resolve eq196361 eq102841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196361
  have eq201088 : y = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq200074
  have eq222159 : y = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq102841
       have i₂ := eq201088
       grind)
    | exact superpose eq201088 eq102841
    | exact resolve eq102841 eq201088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102841 eq201088
  have eq222462 : y = (σ y) ∨ y = (M.op x x) := by grind
  clear eq222159
  have eq222465 : y = (M.op x x) := by
    first
    | (have r₁ := eq222462
       have r₂ := eq145040
       grind)
    | exact resolve eq222462 eq145040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145040 eq222462
  have eq226650 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X1 y) ∨ y = (k x x) := by
    intro X0 X1
    first
    | (have i₁ := eq259 x X1 x x
       have i₂ := eq222465
       grind)
    | exact superpose eq222465 eq259
    | exact resolve eq259 eq222465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq226742 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq551 X0 X1 x x
       have i₂ := eq222465
       grind)
    | exact superpose eq222465 eq551
    | exact resolve eq551 eq222465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq226743 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq553 X0 X1 X2 x x
       have i₂ := eq222465
       grind)
    | exact superpose eq222465 eq553
    | exact resolve eq553 eq222465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq226800 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq974 X0 X1 X2 x x
       have i₂ := eq222465
       grind)
    | exact superpose eq222465 eq974
    | exact resolve eq974 eq222465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974
  have eq226802 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq977 X0 X1 x x
       have i₂ := eq222465
       grind)
    | exact superpose eq222465 eq977
    | exact resolve eq977 eq222465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq226813 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2163 X0 x x
       have i₂ := eq222465
       grind)
    | exact superpose eq222465 eq2163
    | exact resolve eq2163 eq222465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2163
  have eq226817 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op X3 (M.op x y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3108 X0 X1 X2 X3 x x
       have i₂ := eq222465
       grind)
    | exact superpose eq222465 eq3108
    | exact resolve eq3108 eq222465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3108
  have eq226818 : ∀ X2 : G, (M.op x y) = (M.op X2 (M.op x y)) := by
    intro X2
    first
    | (have i₁ := eq226800 x x X2
       have i₂ := eq226802 x x
       grind)
    | exact superpose eq226802 eq226800
    | exact resolve eq226800 eq226802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226800
  have eq226844 : ∀ X1 : G, (M.op x y) = (M.op X1 y) ∨ y = (k x x) := by
    intro X1
    first
    | (have i₁ := eq226650 x X1
       have i₂ := eq226802 x X1
       grind)
    | exact superpose eq226802 eq226650
    | exact resolve eq226650 eq226802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226650
  have eq230904 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X2) X1)) = X0 ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X2 X2) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq865 X2 (M.op X2 x) X1 X2 x
       have i₂ := eq1492 (M.op X2 (M.op X2 x)) X2 X0
       grind)
    | (have i₁ := eq865 X0 X1 X2 x x
       have i₂ := eq1492 X0 X1 (M.op (M.op x (M.op x x)) (M.op X0 (M.op X0 X1)))
       grind)
    | exact superpose eq1492 eq865
    | (have j1 := eq1492 X0 X2 X0
       grind)
    | exact resolve eq865 eq1492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865 eq1492
  have eq231028 : ∀ X0 X2 : G, (M.op X2 X2) = (k X2 X2) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op x y) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq230904 X0 x X2
       have i₂ := eq226802 x (M.op X2 X2)
       grind)
    | exact superpose eq226802 eq230904
    | (have j0 := eq230904 X2 x X2
       grind)
    | exact resolve eq230904 eq226802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230904
  have eq241343 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2266 (M.op x y)
       have i₂ := eq226813 (M.op x y)
       grind)
    | exact superpose eq226813 eq2266
    | (have j0 := eq2266 (M.op x y)
       grind)
    | exact resolve eq2266 eq226813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226813
  have eq241368 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq241343
  have eq290716 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) ≠ (M.op X2 (M.op (σ X0) X2)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1606 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1606
  have eq290717 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op x y) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq290716 X0 X1 x
       have i₂ := eq226802 x (σ X0)
       grind)
    | exact superpose eq226802 eq290716
    | (have j0 := eq290716 X0 X1 x
       grind)
    | exact resolve eq290716 eq226802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226802 eq290716
  have eq291930 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 y) ∨ y = (k x x) ∨ y = (k x x) := by
    intro X0 X1
    first
    | (have i₁ := eq226844 X0
       have i₂ := eq226844 X1
       grind)
    | (have i₁ := eq226844 X1
       have i₂ := eq226844 x
       grind)
    | exact superpose eq226844 eq226844
    | exact resolve eq226844 eq226844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226844
  have eq292638 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 y) ∨ y = (k x x) := by
    intro X0 X1
    first
    | (have j0 := eq291930 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291930
  have eq533190 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq226743 (σ (M.op x y)) (σ (M.op x y)) X0
       have i₂ := eq241368
       grind)
    | exact superpose eq241368 eq226743
    | exact resolve eq226743 eq241368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226743
  have eq533198 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq226817 X0 (σ (M.op x y)) (σ (M.op x y)) X1
       have i₂ := eq241368
       grind)
    | exact superpose eq241368 eq226817
    | exact resolve eq226817 eq241368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226817
  have eq533203 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq533198 X0 X1
       have i₂ := eq241368
       grind)
    | exact superpose eq241368 eq533198
    | exact resolve eq533198 eq241368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533198
  have eq533210 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq533190 X0
       have i₂ := eq241368
       grind)
    | exact superpose eq241368 eq533190
    | exact resolve eq533190 eq241368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241368 eq533190
  have eq533379 : ∀ X0 : G, (M.op x y) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq533203 X0 x
       have i₂ := eq226818 x
       grind)
    | exact superpose eq226818 eq533203
    | exact resolve eq533203 eq226818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533203
  have eq533382 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq533210 x
       have i₂ := eq226818 x
       grind)
    | exact superpose eq226818 eq533210
    | exact resolve eq533210 eq226818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226818 eq533210
  have eq546105 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 (σ (M.op X0 y))) ∨ y = (k x x) := by
    intro X0 X1
    first
    | (have i₁ := eq533379 X0
       have i₂ := eq292638 X0 x
       grind)
    | (have i₁ := eq533379 X0
       have i₂ := eq292638 x X1
       grind)
    | exact superpose eq292638 eq533379
    | exact resolve eq533379 eq292638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292638 eq533379
  have eq666214 : ∀ X0 X1 : G, (M.op x y) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq290717 (τ X1) (τ X0)
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq290717
    | exact resolve eq290717 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq290717
  have eq666246 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op x y) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq666214 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq666214
    | (have j0 := eq666214 X0 X1
       grind)
    | exact resolve eq666214 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666214
  have eq666252 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq666246 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq666246
    | (have j0 := eq666246 X0 X1
       grind)
    | exact resolve eq666246 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666246
  have eq666258 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq666252 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq666252
    | (have j0 := eq666252 X0 X1
       grind)
    | exact resolve eq666252 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666252
  have eq666260 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op x y) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq666258 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq666258
    | (have j0 := eq666258 X0 X1
       grind)
    | exact resolve eq666258 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666258
  have eq828061 : y = (M.op x y) ∨ (M.op x x) = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq85099
       have i₂ := eq231028 y x
       grind)
    | exact superpose eq231028 eq85099
    | (have j1 := eq231028 x x
       grind)
    | exact resolve eq85099 eq231028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85099 eq231028
  have eq828069 : y = (M.op x y) ∨ (M.op x x) = (k x x) := by grind
  clear eq828061
  have eq828080 : y = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq828069
       have i₂ := eq222465
       grind)
    | exact superpose eq222465 eq828069
    | exact resolve eq828069 eq222465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828069
  have eq847928 : ∀ X0 : G, y = (k X0 y) ∨ y = (k x x) := by
    intro X0
    first
    | (have i₁ := eq6696 x x x
       have i₂ := eq222465
       grind)
    | exact superpose eq222465 eq6696
    | exact resolve eq6696 eq222465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6696
  have eq848080 : ∀ X0 : G, y ≠ (M.op x y) ∨ y = (M.op X0 y) ∨ y = (k x x) := by
    intro X0
    first
    | (have i₁ := eq666260 X0 y
       have i₂ := eq847928 X0
       grind)
    | exact superpose eq847928 eq666260
    | exact resolve eq666260 eq847928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666260 eq847928
  have eq848170 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (k x x) := by
    intro X0
    first
    | (have j0 := eq848080 X0
       grind)
    | (have r₁ := eq848080 X0
       have r₂ := eq828080
       grind)
    | exact resolve eq848080 eq828080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848080
  have eq848450 : ∀ X1 : G, y = (M.op X1 (σ y)) ∨ y = (k x x) ∨ y = (k x x) := by
    intro X1
    first
    | (have i₁ := eq546105 x X1
       have i₂ := eq848170 x
       grind)
    | exact superpose eq848170 eq546105
    | exact resolve eq546105 eq848170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546105 eq848170
  have eq849056 : ∀ X1 : G, y = (M.op X1 (σ y)) ∨ y = (k x x) := by
    intro X1
    first
    | (have j0 := eq848450 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848450
  have eq850561 : y ≠ (σ (M.op x y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq849056 (σ x)
       grind)
    | exact superpose eq849056 eq14
    | exact resolve eq14 eq849056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849056
  have eq850577 : y ≠ (M.op x y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq850561
       have i₂ := eq533382
       grind)
    | exact superpose eq533382 eq850561
    | exact resolve eq850561 eq533382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850561
  have eq850908 : y = (k x x) := by
    first
    | (have r₁ := eq850577
       have r₂ := eq828080
       grind)
    | exact resolve eq850577 eq828080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828080 eq850577
  have eq851212 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2266 x
       have i₂ := eq850908
       grind)
    | exact superpose eq850908 eq2266
    | (have j0 := eq2266 x
       grind)
    | exact resolve eq2266 eq850908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2266
  have eq854606 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq17220 x x x x
       have i₂ := eq850908
       grind)
    | exact superpose eq850908 eq17220
    | exact resolve eq17220 eq850908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17220 eq850908
  have eq854885 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq854606 x x
       have i₂ := eq226742 x x
       grind)
    | exact superpose eq226742 eq854606
    | exact resolve eq854606 eq226742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226742 eq854606
  have eq857116 : (M.op x y) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq854885
       grind)
    | exact superpose eq854885 eq14
    | exact resolve eq14 eq854885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854885
  have eq857446 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq857116
       have r₂ := eq533382
       grind)
    | exact resolve eq857116 eq533382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857116
  have eq857518 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq857446
       grind)
    | exact superpose eq857446 eq14
    | exact resolve eq14 eq857446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq857540 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq851212
       have i₂ := eq857446
       grind)
    | exact superpose eq857446 eq851212
    | (have r₁ := eq851212
       have r₂ := eq857446
       grind)
    | exact resolve eq851212 eq857446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851212
  have eq857541 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq857446
       grind)
    | exact superpose eq857446 eq9
    | exact resolve eq9 eq857446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857446
  have eq857622 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq857540
  have eq857651 : x = y := by
    first
    | (have i₁ := eq857541
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq857541
    | exact resolve eq857541 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857541
  have eq857652 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq857518
       have i₂ := eq857622
       grind)
    | exact superpose eq857622 eq857518
    | exact resolve eq857518 eq857622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857518 eq857622
  have eq857656 : (M.op x y) ≠ (σ x) := by
    first
    | (have i₁ := eq857652
       have i₂ := eq533382
       grind)
    | exact superpose eq533382 eq857652
    | exact resolve eq857652 eq533382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857652
  have eq857660 : (σ x) ≠ (M.op x x) := by
    first
    | (have i₁ := eq857656
       have i₂ := eq857651
       grind)
    | exact superpose eq857651 eq857656
    | exact resolve eq857656 eq857651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857656
  have eq857664 : y ≠ (σ x) := by
    first
    | (have i₁ := eq857660
       have i₂ := eq222465
       grind)
    | exact superpose eq222465 eq857660
    | exact resolve eq857660 eq222465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857660
  have eq857668 : x ≠ (σ x) := by
    first
    | (have i₁ := eq857664
       have i₂ := eq857651
       grind)
    | exact superpose eq857651 eq857664
    | exact resolve eq857664 eq857651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857664
  have eq857831 : (M.op x x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq533382
       have i₂ := eq857651
       grind)
    | exact superpose eq857651 eq533382
    | exact resolve eq533382 eq857651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533382
  have eq857902 : y = (σ y) := by
    first
    | (have i₁ := eq857831
       have i₂ := eq222465
       grind)
    | exact superpose eq222465 eq857831
    | exact resolve eq857831 eq222465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222465 eq857831
  have eq858016 : x = (σ x) := by
    first
    | (have i₁ := eq857902
       have i₂ := eq857651
       grind)
    | exact superpose eq857651 eq857902
    | exact resolve eq857902 eq857651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857651 eq857902
  have eq858053 : False := by grind
  exact eq858053

/-- `Equation4301`: `x ◇ (x ◇ y) = z ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pyx_pxy_Equation4301 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4301 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4301.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X0 X2)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X1 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 x X3
       have i₂ := eq8 X1 x X0
       grind)
    | (have i₁ := eq8 X0 X0 x
       have i₂ := eq8 X0 X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X1 X3) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 (M.op X1 X3)
       have i₂ := eq8 X1 X3 X0
       grind)
    | (have i₁ := eq8 X2 X1 (M.op X0 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq95 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X3)) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X1 X2) X3
       have i₂ := eq24 X2 X1 X0
       grind)
    | (have i₁ := eq8 X2 (M.op X1 X2) X3
       have i₂ := eq24 X0 X1 X2
       grind)
    | exact superpose eq24 eq8
    | exact resolve eq8 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq417 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq691 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X2 X3 (M.op X0 X3)
       have i₂ := eq26 X3 X0 X1 X3
       grind)
    | exact superpose eq26 eq24
    | exact resolve eq24 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq26
  have eq1157 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X3 (M.op X4 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq95 X3 X4 X2 X2
       have i₂ := eq691 X2 X2 X0 X1
       grind)
    | (have i₁ := eq95 X0 X1 X3 X2
       have i₂ := eq691 X0 X1 X2 X3
       grind)
    | exact superpose eq691 eq95
    | exact resolve eq95 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1162 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq95 X1 x X1 X0
       have i₂ := eq691 X1 (M.op x X1) X2 X3
       grind)
    | (have i₁ := eq95 X3 X1 (M.op X1 X3) X3
       have i₂ := eq691 X0 X1 (M.op X1 X3) X3
       grind)
    | exact superpose eq691 eq95
    | exact resolve eq95 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq691
  have eq2460 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq52 x y
       grind)
    | exact superpose eq52 eq14
    | (have j1 := eq52 x y
       grind)
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq3591 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq417 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq3614 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq3591 (σ X0)
       grind)
    | exact superpose eq3591 eq13
    | exact resolve eq13 eq3591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3625 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3614 X0
       have i₂ := eq3591 X0
       grind)
    | exact superpose eq3591 eq3614
    | exact resolve eq3614 eq3591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3591 eq3614
  have eq3840 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1162 X1 X2 (σ X0) (σ X0)
       have i₂ := eq3625 X0
       grind)
    | exact superpose eq3625 eq1162
    | exact resolve eq1162 eq3625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18634 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq55
    | exact resolve eq55 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq18842 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18634 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq18634
    | (have j0 := eq18634 X0 X1
       grind)
    | exact resolve eq18634 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18634
  have eq82558 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2460
       have i₂ := eq18842 y x
       grind)
    | exact superpose eq18842 eq2460
    | (have j1 := eq18842 (σ y) (σ x)
       grind)
    | (have r₁ := eq2460
       have r₂ := eq18842 y x
       grind)
    | exact resolve eq2460 eq18842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2460 eq18842
  have eq82559 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq82558
  have eq82563 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq82559
       have i₂ := eq3625 x
       grind)
    | exact superpose eq3625 eq82559
    | exact resolve eq82559 eq3625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82559
  have eq82571 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq82563
       grind)
    | exact superpose eq82563 eq9
    | exact resolve eq9 eq82563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82563
  have eq82615 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq82571
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq82571
    | exact resolve eq82571 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82571
  have eq82616 : y = (M.op x x) := by grind
  clear eq82615
  have eq82827 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3840 x X0 X1
       have i₂ := eq82616
       grind)
    | exact superpose eq82616 eq3840
    | exact resolve eq3840 eq82616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82956 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1157 X0 X1 X2 x x
       have i₂ := eq82616
       grind)
    | exact superpose eq82616 eq1157
    | exact resolve eq1157 eq82616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157
  have eq82958 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1162 X0 X1 x x
       have i₂ := eq82616
       grind)
    | exact superpose eq82616 eq1162
    | exact resolve eq1162 eq82616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162 eq82616
  have eq82972 : ∀ X2 : G, (M.op x y) = (M.op X2 (M.op x y)) := by
    intro X2
    first
    | (have i₁ := eq82956 x x X2
       have i₂ := eq82958 x x
       grind)
    | exact superpose eq82958 eq82956
    | exact resolve eq82956 eq82958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82956
  have eq82996 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq82827 x x
       have i₂ := eq82958 x x
       grind)
    | exact superpose eq82958 eq82827
    | exact resolve eq82827 eq82958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82827
  have eq92827 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq3840 (M.op x y) X0 X1
       have i₂ := eq82972 (M.op x y)
       grind)
    | exact superpose eq82972 eq3840
    | exact resolve eq3840 eq82972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3840
  have eq93152 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (σ (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq92827 X0 X1
       have i₂ := eq3625 (M.op x y)
       grind)
    | exact superpose eq3625 eq92827
    | exact resolve eq92827 eq3625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3625 eq92827
  have eq93218 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq93152 X0 X1
       have i₂ := eq82972 (M.op x y)
       grind)
    | exact superpose eq82972 eq93152
    | exact resolve eq93152 eq82972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82972 eq93152
  have eq93253 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq93218 x x
       have i₂ := eq82958 x x
       grind)
    | exact superpose eq82958 eq93218
    | exact resolve eq93218 eq82958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82958 eq93218
  have eq100236 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq82996
       grind)
    | exact superpose eq82996 eq14
    | exact resolve eq14 eq82996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82996
  have eq100504 : False := by grind
  exact eq100504
