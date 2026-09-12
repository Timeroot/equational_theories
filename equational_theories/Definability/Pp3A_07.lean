import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(X,Y) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_x_pyx_pxy_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq58 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq58 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq203 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq16 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
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
  have eq205 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq16 X0 X3 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
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
  have eq209 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq426 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq342 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq342
    | exact resolve eq342 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq574 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq203 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq203 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq203 eq203
    | exact resolve eq203 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq601 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq574 X0 X2
       grind)
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq574 X2 X0
       grind)
    | exact superpose eq574 eq16
    | exact resolve eq16 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq605 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X2 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 (M.op X1 X1)
       have i₂ := eq574 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq16 X2 X1 (M.op X1 X1)
       have i₂ := eq574 (M.op X1 X1) X0
       grind)
    | exact superpose eq574 eq16
    | exact resolve eq16 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq684 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X0) = (M.op (M.op X2 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq203 (M.op X1 X1) X1 (M.op (M.op X2 X2) X0)
       have i₂ := eq601 (M.op X1 X1) X2 X0
       grind)
    | exact superpose eq601 eq203
    | exact resolve eq203 eq601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq967 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq208
       grind)
    | exact superpose eq208 eq41
    | exact resolve eq41 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq208
  have eq968 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq967
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq967
    | exact resolve eq967 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967
  have eq970 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq20 eq968
    | exact resolve eq968 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968
  have eq1098 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq970 eq209
    | exact resolve eq209 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq970
  have eq1105 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq1098
       have r₂ := eq27
       grind)
    | exact resolve eq1098 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098
  have eq1131 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 X0) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1105 eq16
    | exact resolve eq16 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105
  have eq1132 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq205 eq1131
    | exact resolve eq1131 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq1131
  have eq1133 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1132
  have eq1159 : ∀ X0 : G, y = (M.op (M.op (M.op X0 X0) y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq16 y X0 y
       have i₂ := eq1133
       grind)
    | exact superpose eq1133 eq16
    | exact resolve eq16 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133
  have eq1160 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq204 eq1159
    | exact resolve eq1159 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq1159
  have eq1161 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1160
  have eq1426 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1161 eq31
    | exact resolve eq31 eq1161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1161
  have eq1448 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq1426
    | exact resolve eq1426 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1426
  have eq1449 : x = y := by grind
  clear eq1448
  have eq1452 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1449
       grind)
    | exact superpose eq1449 eq18
    | exact resolve eq18 eq1449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1453 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1449
       grind)
    | exact superpose eq1449 eq24
    | exact resolve eq24 eq1449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1449
  have eq1460 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1453
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1453
    | exact resolve eq1453 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1453
  have eq1461 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1460 eq26
    | exact resolve eq26 eq1460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1460
  have eq1488 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 x X0
       have i₂ := eq1452
       grind)
    | exact superpose eq1452 eq16
    | exact resolve eq16 eq1452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1489 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 (M.op x y)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq203 X0 x X1
       have i₂ := eq1452
       grind)
    | exact superpose eq1452 eq203
    | exact resolve eq203 eq1452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq1492 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op x y) (M.op X2 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq206 X2 x X1 X0
       have i₂ := eq1452
       grind)
    | exact superpose eq1452 eq206
    | exact resolve eq206 eq1452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1496 : ∀ X0 : G, (M.op x y) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq574 x X0
       have i₂ := eq1452
       grind)
    | exact superpose eq1452 eq574
    | exact resolve eq574 eq1452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1503 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 (M.op x y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq605 X0 x X1
       have i₂ := eq1452
       grind)
    | exact superpose eq1452 eq605
    | exact resolve eq605 eq1452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq1506 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq684 X1 X0 x
       have i₂ := eq1452
       grind)
    | exact superpose eq1452 eq684
    | exact resolve eq684 eq1452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684 eq1452
  have eq1511 : ∀ X1 : G, (M.op (M.op x y) (M.op X1 (M.op x y))) = X1 := by
    intro X1
    first
    | (have i₁ := eq1503 x X1
       have i₂ := eq1506 x (M.op X1 sF0)
       grind)
    | exact superpose eq1506 eq1503
    | exact resolve eq1503 eq1506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503
  have eq1518 : ∀ X1 X2 : G, (M.op (M.op x y) X1) = (M.op (M.op (M.op x y) (M.op X2 X1)) X2) := by
    intro X1 X2
    first
    | (have i₁ := eq1492 x X1 X2
       have i₂ := eq1506 x X1
       grind)
    | exact superpose eq1506 eq1492
    | exact resolve eq1492 eq1506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1492
  have eq1534 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq1461 eq574
    | exact resolve eq574 eq1461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq1461
  have eq1559 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1534 x
       have i₂ := eq1496 x
       grind)
    | exact superpose eq1496 eq1534
    | exact resolve eq1534 eq1496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1534
  have eq1583 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq1559 eq27
    | exact resolve eq27 eq1559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1559
  have eq2459 : ∀ X0 X1 : G, (k (M.op (M.op x y) X1) (M.op X0 X1)) = X0 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | exact superpose eq1488 eq11
    | (have j0 := eq11 (k (M.op (M.op x y) X1) (M.op X0 X1)) X0
       grind)
    | exact resolve eq11 eq1488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488
  have eq2462 : ∀ X0 X1 : G, (k (M.op (M.op x y) X1) (M.op X0 X1)) = X0 ∨ (M.op x y) = X0 ∨ (M.op X0 X1) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2459 X0 X1
       have i₂ := eq1496 (M.op X0 X1)
       grind)
    | exact superpose eq1496 eq2459
    | (have j0 := eq2459 X0 X1
       grind)
    | exact resolve eq2459 eq1496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2459
  have eq2607 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op x y)))) = (M.op (M.op (M.op X3 X3) X0) X2) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1489 eq206
    | exact resolve eq206 eq1489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq2608 : ∀ X0 X1 : G, (k X1 (M.op X0 (M.op X1 (M.op x y)))) = X0 ∨ (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op X0 (M.op X1 (M.op x y)))) = X0 ∨ (M.op X0 (M.op X1 (M.op x y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1489 eq11
    | (have j0 := eq11 (k X1 (M.op X0 (M.op X1 (M.op x y)))) X0
       grind)
    | exact resolve eq11 eq1489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489
  have eq2631 : ∀ X0 X1 : G, (k X1 (M.op X0 (M.op X1 (M.op x y)))) = X0 ∨ (M.op x y) = X0 ∨ (M.op X0 (M.op X1 (M.op x y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2608 X0 X1
       have i₂ := eq1496 (M.op X0 (M.op X1 sF0))
       grind)
    | exact superpose eq1496 eq2608
    | (have j0 := eq2608 X0 X1
       grind)
    | exact resolve eq2608 eq1496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2608
  have eq2632 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op x y)))) = (M.op (M.op (M.op x y) X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2607 X0 X1 X2 x
       have i₂ := eq1506 x X0
       grind)
    | exact superpose eq1506 eq2607
    | exact resolve eq2607 eq1506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2607
  have eq2664 : ∀ X0 X2 : G, (M.op (M.op x y) (M.op X0 (M.op X2 (M.op x y)))) = (M.op (M.op (M.op x y) X0) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq2632 X0 X0 X2
       have i₂ := eq1506 X0 (M.op X0 (M.op X2 sF0))
       grind)
    | exact superpose eq1506 eq2632
    | exact resolve eq2632 eq1506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1506 eq2632
  have eq3895 : ∀ X0 X1 : G, (τ (k X0 X1)) ≠ (M.op (τ X1) (τ X1)) ∨ (M.op (τ X1) (τ X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq215 (τ X0) (τ X1)
       have i₂ := eq426 X1 X0
       grind)
    | exact superpose eq426 eq215
    | (have j0 := eq215 (τ X0) (τ X1)
       grind)
    | exact resolve eq215 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq426
  have eq3896 : ∀ X0 X1 : G, (M.op x y) ≠ (τ (k X0 X1)) ∨ (M.op (τ X1) (τ X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3895 X0 X1
       have i₂ := eq1496 (τ X1)
       grind)
    | exact superpose eq1496 eq3895
    | (have j0 := eq3895 X0 X1
       grind)
    | exact resolve eq3895 eq1496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3895
  have eq3917 : ∀ X0 X1 : G, (M.op x y) ≠ (τ (k X0 X1)) ∨ (M.op x y) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3896 X0 X1
       have i₂ := eq1496 (τ X1)
       grind)
    | exact superpose eq1496 eq3896
    | (have j0 := eq3896 X0 X1
       grind)
    | exact resolve eq3896 eq1496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3896
  have eq5372 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X1 (M.op x y))) = (M.op (M.op (M.op (M.op x y) X0) X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq2664 eq1518
    | exact resolve eq1518 eq2664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518 eq2664
  have eq5401 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) X0) X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5372 X0 X1
       have i₂ := eq1511 (M.op sF0 (M.op X1 sF0))
       grind)
    | exact superpose eq1511 eq5372
    | exact resolve eq5372 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5372
  have eq5463 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op x y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1511 eq5401
    | exact resolve eq5401 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5401
  have eq17997 : ∀ X0 : G, (τ X0) = (k (M.op x y) (τ (M.op X0 (M.op (σ (M.op x y)) (M.op x y))))) ∨ (M.op x y) = X0 ∨ (σ (M.op x y)) = (M.op X0 (M.op (σ (M.op x y)) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq2631 eq139
    | (have j1 := eq2631 X0 (σ (M.op x y))
       grind)
    | exact resolve eq139 eq2631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2631
  have eq30596 : (τ (M.op (σ (M.op x y)) (M.op x y))) = (k (M.op x y) (τ (M.op x y))) ∨ (M.op x y) = (M.op (σ (M.op x y)) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq17997 (M.op sF1 sF0)
       have i₂ := eq1496 (M.op sF1 sF0)
       grind)
    | exact superpose eq1496 eq17997
    | (have j0 := eq17997 (M.op (σ (M.op x y)) (M.op x y))
       grind)
    | exact resolve eq17997 eq1496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17997
  have eq30669 : (τ (M.op (σ (M.op x y)) (M.op x y))) = (k (M.op x y) (τ (M.op x y))) ∨ (M.op x y) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | (have r₁ := eq30596
       have r₂ := eq1583
       grind)
    | exact resolve eq30596 eq1583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30596
  have eq30722 : (M.op (σ (M.op x y)) (M.op x y)) = (σ (k (M.op x y) (τ (M.op x y)))) ∨ (M.op x y) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq30669 eq14
    | exact resolve eq14 eq30669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30669
  have eq30733 : (M.op (σ (M.op x y)) (M.op x y)) = (k (σ (M.op x y)) (M.op x y)) ∨ (M.op x y) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq30722
       have i₂ := eq39 sF0 sF0
       grind)
    | exact superpose eq39 eq30722
    | exact resolve eq30722 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq30722
  have eq30735 : (M.op (σ (M.op x y)) (M.op x y)) = (k (σ (M.op x y)) (M.op x y)) ∨ (M.op x y) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq20 eq30733
    | exact resolve eq30733 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq30733
  have eq30768 : (σ (M.op x y)) = (k (M.op (M.op x y) (M.op x y)) (k (σ (M.op x y)) (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op (M.op x y) (M.op x y)) = (k (σ (M.op x y)) (M.op x y)) ∨ (M.op x y) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq30735 eq2462
    | (have j0 := eq2462 (σ (M.op x y)) x
       grind)
    | exact resolve eq2462 eq30735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2462
  have eq30772 : (M.op x y) ≠ (k (σ (M.op x y)) (M.op x y)) ∨ (M.op x y) = (M.op (σ (M.op x y)) (M.op x y)) := by grind
  clear eq30735
  have eq30773 : (σ (M.op x y)) = (k (M.op (M.op x y) (M.op x y)) (k (σ (M.op x y)) (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = (k (σ (M.op x y)) (M.op x y)) ∨ (M.op x y) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | (have r₁ := eq30768
       have r₂ := eq1583
       grind)
    | exact resolve eq30768 eq1583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30768
  have eq30783 : (σ (M.op x y)) = (k (M.op x y) (k (σ (M.op x y)) (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = (k (σ (M.op x y)) (M.op x y)) ∨ (M.op x y) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq30773
       have i₂ := eq1496 sF0
       grind)
    | exact superpose eq1496 eq30773
    | exact resolve eq30773 eq1496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30773
  have eq30789 : (M.op x y) = (k (σ (M.op x y)) (M.op x y)) ∨ (σ (M.op x y)) = (k (M.op x y) (k (σ (M.op x y)) (M.op x y))) ∨ (M.op x y) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq30783
       have i₂ := eq1496 sF0
       grind)
    | exact superpose eq1496 eq30783
    | exact resolve eq30783 eq1496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30783
  have eq30792 : (σ (M.op x y)) = (k (M.op x y) (k (σ (M.op x y)) (M.op x y))) ∨ (M.op x y) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | (have r₁ := eq30789
       have r₂ := eq30772
       grind)
    | exact resolve eq30789 eq30772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30789
  have eq30908 : (M.op x y) ≠ (τ (σ (M.op x y))) ∨ (M.op x y) = (M.op (τ (M.op x y)) (τ (k (σ (M.op x y)) (M.op x y)))) ∨ (τ (M.op x y)) = (τ (k (σ (M.op x y)) (M.op x y))) ∨ (M.op x y) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq30792 eq3917
    | (have j0 := eq3917 (M.op x y) (k (σ (M.op x y)) (M.op x y))
       grind)
    | exact resolve eq3917 eq30792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3917 eq30792
  have eq30929 : (M.op x y) = (M.op (τ (M.op x y)) (τ (k (σ (M.op x y)) (M.op x y)))) ∨ (τ (M.op x y)) = (τ (k (σ (M.op x y)) (M.op x y))) ∨ (M.op x y) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | (have r₁ := eq30908
       have r₂ := eq28
       grind)
    | exact resolve eq30908 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq30908
  have eq30941 : (M.op x y) = (M.op (τ (M.op x y)) (k (M.op x y) (τ (M.op x y)))) ∨ (τ (M.op x y)) = (τ (k (σ (M.op x y)) (M.op x y))) ∨ (M.op x y) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq139 eq30929
    | exact resolve eq30929 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30929
  have eq30950 : (M.op x y) = (M.op (τ (M.op x y)) (k (M.op x y) (τ (M.op x y)))) ∨ (τ (M.op x y)) = (k (M.op x y) (τ (M.op x y))) ∨ (M.op x y) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq139 eq30941
    | exact resolve eq30941 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq30941
  have eq54976 : (k (M.op x y) (τ (M.op x y))) = (M.op (M.op x y) (M.op (τ (M.op x y)) (M.op x y))) ∨ (τ (M.op x y)) = (k (M.op x y) (τ (M.op x y))) ∨ (M.op x y) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq30950 eq5463
    | exact resolve eq5463 eq30950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5463 eq30950
  have eq54992 : (τ (M.op x y)) = (k (M.op x y) (τ (M.op x y))) ∨ (τ (M.op x y)) = (k (M.op x y) (τ (M.op x y))) ∨ (M.op x y) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq54976
       have i₂ := eq1511 (M.op sF0 (M.op (τ sF0) sF0))
       grind)
    | exact superpose eq1511 eq54976
    | exact resolve eq54976 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54976
  have eq54993 : (τ (M.op x y)) = (k (M.op x y) (τ (M.op x y))) ∨ (M.op x y) = (M.op (σ (M.op x y)) (M.op x y)) := by grind
  clear eq54992
  have eq55009 : (σ (τ (M.op x y))) = (k (σ (M.op x y)) (σ (τ (M.op x y)))) ∨ (M.op x y) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq54993 eq38
    | exact resolve eq38 eq54993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq54993
  have eq55052 : (M.op x y) = (k (σ (M.op x y)) (M.op x y)) ∨ (M.op x y) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq55009
       have i₂ := eq14 sF0
       grind)
    | exact superpose eq14 eq55009
    | exact resolve eq55009 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55009
  have eq55060 : (M.op x y) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | (have r₁ := eq55052
       have r₂ := eq30772
       grind)
    | exact resolve eq55052 eq30772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30772 eq55052
  have eq55076 : (σ (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq55060 eq1511
    | exact resolve eq1511 eq55060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511 eq55060
  have eq55154 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq55076
       have i₂ := eq1496 sF0
       grind)
    | exact superpose eq1496 eq55076
    | exact resolve eq55076 eq1496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1496 eq55076
  have eq55166 : False := by grind
  exact eq55166

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_y_pxy_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq16 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (k X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X0 X1 X2
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq176
    | exact resolve eq176 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq186 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) X1) (M.op X2 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq445 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq323 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq323
    | exact resolve eq323 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq647 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq183 X0 X2 (M.op (M.op X1 X1) (k X2 X2))
       have i₂ := eq16 X0 X1 (k X2 X2)
       grind)
    | exact superpose eq16 eq183
    | exact resolve eq183 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq652 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (k X1 X1) (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq647 X0 X1 X2
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq647
    | exact resolve eq647 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq654 : ∀ X0 X1 X2 : G, (M.op (M.op (τ (k X0 X0)) X1) (M.op X2 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq186 (τ X0) X1 X2
       have i₂ := eq445 X0 X0
       grind)
    | exact superpose eq445 eq186
    | exact resolve eq186 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq652 X1 x x
       have i₂ := eq652 X0 x x
       grind)
    | (have i₁ := eq652 X0 X1 X1
       have i₂ := eq652 (k X1 X1) X1 x
       grind)
    | exact superpose eq652 eq652
    | exact resolve eq652 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq757 : ∀ X0 X1 X2 : G, (M.op (M.op (k X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq186 X1 X2 X2
       have i₂ := eq698 X0 X2
       grind)
    | (have i₁ := eq186 X1 X2 X2
       have i₂ := eq698 X2 X0
       grind)
    | exact superpose eq698 eq186
    | exact resolve eq186 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq698
  have eq773 : ∀ X0 X1 X2 : G, (M.op (M.op (k X1 X1) X2) (k X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq757 X0 X1 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq757
    | exact resolve eq757 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq1319 : (M.op x y) = (k x y) ∨ (M.op y y) = (M.op y x) ∨ x = y := by
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
  have eq1320 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
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
  have eq1322 : (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1320
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq1320
    | exact resolve eq1320 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320
  have eq1323 : (k y y) = (M.op y x) ∨ (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq1319
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq1319
    | exact resolve eq1319 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319
  have eq3832 : ∀ X0 X1 X2 : G, (M.op (M.op (τ (k X0 X0)) X1) (k X2 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq773 X2 (τ X0) X1
       have i₂ := eq445 X0 X0
       grind)
    | exact superpose eq445 eq773
    | exact resolve eq773 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445 eq773
  have eq8865 : ∀ X0 : G, (σ y) = (M.op (M.op (τ (k X0 X0)) (σ x)) (k (σ y) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq1322 eq654
    | exact resolve eq654 eq1322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322
  have eq8868 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8865 x
       have i₂ := eq3832 x sF2 sF3
       grind)
    | exact superpose eq3832 eq8865
    | exact resolve eq8865 eq3832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8865
  have eq8869 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq8868
  have eq9233 : ∀ X0 : G, y = (M.op (M.op (τ (k X0 X0)) x) (k y y)) ∨ (M.op x y) = (k x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq654 X0 x y
       have i₂ := eq1323
       grind)
    | exact superpose eq1323 eq654
    | exact resolve eq654 eq1323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654 eq1323
  have eq9236 : x = y ∨ (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq9233 x
       have i₂ := eq3832 x x y
       grind)
    | exact superpose eq3832 eq9233
    | exact resolve eq9233 eq3832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3832 eq9233
  have eq9237 : (M.op x y) = (k x y) ∨ x = y := by grind
  clear eq9236
  have eq9248 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq9237
       grind)
    | exact superpose eq9237 eq40
    | exact resolve eq40 eq9237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq9237
  have eq9249 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq9248
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9248
    | exact resolve eq9248 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9248
  have eq9251 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq9249
    | exact resolve eq9249 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9249
  have eq9254 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq9251 eq8869
    | exact resolve eq8869 eq9251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8869 eq9251
  have eq9261 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq9254
       have r₂ := eq27
       grind)
    | exact resolve eq9254 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9254
  have eq9266 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq9261 eq31
    | exact resolve eq31 eq9261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq9261
  have eq9291 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq9266
    | exact resolve eq9266 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq9266
  have eq9292 : x = y := by grind
  clear eq9291
  have eq9295 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq9292
       grind)
    | exact superpose eq9292 eq18
    | exact resolve eq18 eq9292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq9296 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq9292
       grind)
    | exact superpose eq9292 eq24
    | exact resolve eq24 eq9292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq9292
  have eq9309 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq9296
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9296
    | exact resolve eq9296 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9296
  have eq9310 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq9295
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq9295
    | exact resolve eq9295 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9295
  have eq9311 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq9309 eq26
    | exact resolve eq26 eq9309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq9309
  have eq9337 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq9311
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq9311
    | exact resolve eq9311 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq9311
  have eq9342 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq9310
       grind)
    | exact superpose eq9310 eq39
    | exact resolve eq39 eq9310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq9310
  have eq9511 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq9342
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9342
    | exact resolve eq9342 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq9342
  have eq9553 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9337 eq9511
    | exact resolve eq9511 eq9337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9337 eq9511
  have eq9581 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq9553
    | exact resolve eq9553 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq9553
  have eq9599 : False := by grind
  exact eq9599

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyy_pyy_pyx_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq28 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 X0 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq28 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq28
    | (have j0 := eq28 y
       grind)
    | exact resolve eq28 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y X0
       grind)
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq29 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29
    | (have j0 := eq29 y
       grind)
    | exact resolve eq29 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq48 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq49 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq53 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq77 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq53 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 x y X0
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq53 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 X0 x y
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq82 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq53 X2 X0 x
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq77 eq53
    | exact resolve eq53 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (k X1 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op x x)
       have i₂ := eq53 x x x
       grind)
    | exact superpose eq53 eq12
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq130 : (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq59
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq59
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq134 : (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq130
    | exact resolve eq130 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq137 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq100 (σ X0)
       grind)
    | exact superpose eq100 eq15
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq137 X0
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq137
    | exact resolve eq137 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq187 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (M.op X1 X1) = (M.op (τ X0) (τ X0)) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq49
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq209 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X1 X1) = (M.op (τ X0) (τ X0)) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) := by
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
  have eq732 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq99 (M.op X0 X1) X1
       have i₂ := eq82 X1 (M.op X0 X1) X0
       grind)
    | exact superpose eq82 eq99
    | (have j0 := eq99 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq99 (M.op x X0) X0
       have r₂ := eq82 X0 (M.op x X0) x
       grind)
    | exact resolve eq99 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq733 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq99 X0 (M.op X0 X1)
       have i₂ := eq53 X0 X0 X1
       grind)
    | exact superpose eq53 eq99
    | (have j0 := eq99 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq99 x (M.op x x)
       have r₂ := eq53 x x x
       grind)
    | exact resolve eq99 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq734 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq83 eq99
    | (have j0 := eq99 (M.op x y) y
       grind)
    | (have r₁ := eq99 (M.op x y) y
       have r₂ := eq83 (M.op x y)
       grind)
    | exact resolve eq99 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq735 : x ≠ x ∨ x = (k (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq80 eq99
    | (have j0 := eq99 x (M.op x y)
       grind)
    | (have r₁ := eq99 x (M.op x y)
       have r₂ := eq80 x
       grind)
    | exact resolve eq99 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq741 : x = (k (M.op x y) (M.op x x)) := by grind
  clear eq735
  have eq742 : (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by grind
  clear eq734
  have eq743 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq733 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq744 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq732 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq838 : (σ y) = (σ (M.op x y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | exact superpose eq742 eq121
    | (have j0 := eq121 (M.op (M.op x y) (M.op x y)) y
       grind)
    | exact resolve eq121 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq840 : (σ x) = (σ (M.op x y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | exact superpose eq741 eq121
    | (have j0 := eq121 (M.op x x) (M.op x y)
       grind)
    | exact resolve eq121 eq741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq873 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq121 X0 X1
       grind)
    | exact superpose eq121 eq10
    | (have j1 := eq121 X0 X1
       grind)
    | exact resolve eq10 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq896 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq873 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq873
    | (have j0 := eq873 X0 X1
       grind)
    | exact resolve eq873 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq911 : (σ x) = (σ (M.op x y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq840
    | exact resolve eq840 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq913 : (σ y) = (σ (M.op x y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | exact superpose eq20 eq838
    | exact resolve eq838 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq931 : (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq911
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq911
    | exact resolve eq911 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq933 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq913
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq913
    | exact resolve eq913 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq941 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq931
       have i₂ := eq138 x
       grind)
    | exact superpose eq138 eq931
    | exact resolve eq931 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931
  have eq943 : (M.op (σ y) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq933
       have i₂ := eq138 sF0
       grind)
    | exact superpose eq138 eq933
    | exact resolve eq933 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933
  have eq949 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq941
       have i₂ := eq53 (σ x) (σ x) (σ x)
       grind)
    | (have i₁ := eq941
       have i₂ := eq53 x (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) x
       grind)
    | exact superpose eq53 eq941
    | exact resolve eq941 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941
  have eq951 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq943
       have i₂ := eq53 (σ sF0) (σ sF0) (σ sF0)
       grind)
    | (have i₁ := eq943
       have i₂ := eq53 x (M.op (M.op (σ sF0) (σ sF0)) (M.op (σ sF0) (σ sF0))) x
       grind)
    | exact superpose eq53 eq943
    | exact resolve eq943 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943
  have eq955 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq949
    | exact resolve eq949 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq957 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq951
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq951
    | exact resolve eq951 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq960 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq955
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq955
    | exact resolve eq955 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq962 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | exact superpose eq20 eq957
    | exact resolve eq957 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq965 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq960
    | exact resolve eq960 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq967 : (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq962
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq962
    | exact resolve eq962 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq970 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq965
       have i₂ := eq138 x
       grind)
    | exact superpose eq138 eq965
    | exact resolve eq965 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965
  have eq972 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq967
       have i₂ := eq138 sF0
       grind)
    | exact superpose eq138 eq967
    | exact resolve eq967 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967
  have eq975 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq970
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq970
    | exact resolve eq970 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq977 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq972
    | exact resolve eq972 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972
  have eq980 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq975
       have i₂ := eq53 sF2 sF2 sF2
       grind)
    | (have i₁ := eq975
       have i₂ := eq53 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq53 eq975
    | exact resolve eq975 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975
  have eq982 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq977
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq977
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq977
    | exact resolve eq977 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq5928 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ X1) (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (k X1 (σ X0)) = X1 ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq744 X1 X1
       have i₂ := eq209 X0 X1
       grind)
    | (have i₁ := eq744 (τ X0) (τ X0)
       have i₂ := eq209 X0 X1
       grind)
    | exact superpose eq209 eq744
    | (have j1 := eq209 X1 X0
       grind)
    | exact resolve eq744 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq744
  have eq6005 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = X1 ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5928 X0 X1
       have i₂ := eq53 X0 X0 X0
       grind)
    | (have i₁ := eq5928 X0 X1
       have i₂ := eq53 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq53 eq5928
    | (have j0 := eq5928 X0 X1
       grind)
    | exact resolve eq5928 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5928
  have eq6086 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq6005 X0 X1
       have j1 := eq12 (τ X1) X0
       grind)
    | (have r₁ := eq6005 (τ X1) X1
       have r₂ := eq12 (τ X1) (τ X1)
       grind)
    | (have r₁ := eq6005 X1 X1
       have r₂ := eq12 (τ X1) X1
       grind)
    | exact resolve eq6005 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6005
  have eq6225 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 (τ X1)
       have i₂ := eq6086 (τ X0) X1
       grind)
    | exact superpose eq6086 eq48
    | (have j1 := eq6086 (τ X0) X1
       grind)
    | exact resolve eq48 eq6086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq6086
  have eq6289 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6225 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6225
    | (have j0 := eq6225 X0 X1
       grind)
    | exact resolve eq6225 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6225
  have eq6323 : ∀ X0 X1 : G, (k X1 X0) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6289 X0 X1
       have i₂ := eq138 (τ X0)
       grind)
    | exact superpose eq138 eq6289
    | (have j0 := eq6289 X0 X1
       grind)
    | exact resolve eq6289 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6289
  have eq6348 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6323 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6323
    | (have j0 := eq6323 X0 X1
       grind)
    | exact resolve eq6323 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6323
  have eq6372 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6348 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6348
    | (have j0 := eq6348 X0 X1
       grind)
    | exact resolve eq6348 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6348
  have eq6555 : (σ (k (M.op x y) y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ (k (M.op x y) y)) := by
    first
    | exact superpose eq34 eq6372
    | exact resolve eq6372 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq6776 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq6372 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6372
  have eq7203 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq6776 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6776
  have eq7206 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq7203 (M.op x x)
       have i₂ := eq53 x x x
       grind)
    | exact superpose eq53 eq7203
    | exact resolve eq7203 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7203
  have eq11186 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ (k (M.op x y) y)) := by grind
  clear eq6555
  have eq13286 : x = (M.op x y) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq741
       have i₂ := eq896 sF0 (M.op x x)
       grind)
    | exact superpose eq896 eq741
    | (have j1 := eq896 (M.op x x) (M.op x y)
       grind)
    | exact resolve eq741 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741 eq896
  have eq13495 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq13286
       have i₂ := eq138 x
       grind)
    | exact superpose eq138 eq13286
    | exact resolve eq13286 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13286
  have eq13662 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq13495
       have i₂ := eq53 (σ x) (σ x) (σ x)
       grind)
    | (have i₁ := eq13495
       have i₂ := eq53 x (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) x
       grind)
    | exact superpose eq53 eq13495
    | exact resolve eq13495 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13495
  have eq13791 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq13662
    | exact resolve eq13662 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13662
  have eq13894 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq13791
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13791
    | exact resolve eq13791 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13791
  have eq13952 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq13894
    | exact resolve eq13894 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13894
  have eq13986 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13952
       have i₂ := eq138 x
       grind)
    | exact superpose eq138 eq13952
    | exact resolve eq13952 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13952
  have eq14019 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13986
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13986
    | exact resolve eq13986 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13986
  have eq14049 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14019
       have i₂ := eq53 sF2 sF2 sF2
       grind)
    | (have i₁ := eq14019
       have i₂ := eq53 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq53 eq14019
    | exact resolve eq14019 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14019
  have eq23545 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq980 eq53
    | exact resolve eq53 eq980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980
  have eq23558 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14049 eq53
    | exact resolve eq53 eq14049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14049
  have eq24948 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq982 eq53
    | exact resolve eq53 eq982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq37211 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq24948 eq23545
    | exact resolve eq23545 eq24948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24948
  have eq37294 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq37211
    | exact resolve eq37211 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37211
  have eq37300 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq37294
       have r₂ := eq27
       grind)
    | exact resolve eq37294 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37294
  have eq37345 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq37300 eq743
    | exact resolve eq743 eq37300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37300
  have eq37353 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq37345
       have i₂ := eq100 sF1
       grind)
    | exact superpose eq100 eq37345
    | exact resolve eq37345 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37345
  have eq37469 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq37353 eq23545
    | exact resolve eq23545 eq37353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23545
  have eq37504 : (σ x) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq37353
  have eq37507 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq37469
  have eq37524 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq37507
       have r₂ := eq37504
       grind)
    | exact resolve eq37507 eq37504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37504 eq37507
  have eq37537 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq37524
    | exact resolve eq37524 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37524
  have eq37539 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq37537
       have r₂ := eq27
       grind)
    | exact resolve eq37537 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37537
  have eq37542 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq37539 eq982
    | exact resolve eq982 eq37539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982
  have eq37586 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq37539 eq743
    | exact resolve eq743 eq37539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37593 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq37542
  have eq37596 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq37586
       have i₂ := eq100 sF2
       grind)
    | exact superpose eq100 eq37586
    | exact resolve eq37586 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37586
  have eq37613 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq37593
    | exact resolve eq37593 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37593
  have eq37618 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq37613
       have r₂ := eq27
       grind)
    | exact resolve eq37613 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37613
  have eq37798 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq37618 eq743
    | exact resolve eq743 eq37618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37618
  have eq37806 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq37798
       have i₂ := eq100 sF1
       grind)
    | exact superpose eq100 eq37798
    | exact resolve eq37798 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37798
  have eq39242 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq37806 eq37539
    | exact resolve eq37539 eq37806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37539 eq37806
  have eq39282 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq39242
  have eq39313 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq39282 eq26
    | exact resolve eq26 eq39282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39317 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq39282 eq39
    | exact resolve eq39 eq39282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39282
  have eq39380 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq38 eq39317
    | exact resolve eq39317 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39317
  have eq39390 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq39380 eq39
    | exact resolve eq39 eq39380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39380
  have eq39439 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq37 eq39390
    | exact resolve eq39390 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39390
  have eq39447 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq39439 eq38
    | exact resolve eq38 eq39439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39439
  have eq39499 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq37 eq39447
    | exact resolve eq39447 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39447
  have eq42676 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq39313 eq37596
    | exact resolve eq37596 eq39313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37596 eq39313
  have eq42717 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq42676
  have eq42729 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq42717
       have r₂ := eq27
       grind)
    | exact resolve eq42717 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42717
  have eq42737 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq42729 eq39
    | exact resolve eq39 eq42729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42729
  have eq42786 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq42737
    | exact resolve eq42737 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42737
  have eq42794 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq42786 eq38
    | exact resolve eq38 eq42786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42786
  have eq42846 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq42794
    | exact resolve eq42794 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq42794
  have eq42850 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42846 eq20
    | exact resolve eq20 eq42846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42851 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq42846 eq77
    | exact resolve eq77 eq42846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq42936 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq42846
  have eq42947 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq42850
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq42850
    | exact resolve eq42850 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42850
  have eq44492 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq42851 (M.op y x)
       have i₂ := eq42851 x
       grind)
    | exact superpose eq42851 eq42851
    | exact resolve eq42851 eq42851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42851
  have eq44505 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq44492
  have eq44533 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq138 y
       have i₂ := eq44505
       grind)
    | exact superpose eq44505 eq138
    | exact resolve eq138 eq44505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44505
  have eq44571 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44533
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq44533
    | exact resolve eq44533 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44533
  have eq44590 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (σ (k (M.op x y) y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq44571 eq11186
    | exact resolve eq11186 eq44571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11186 eq44571
  have eq44659 : (σ (M.op x y)) = (σ (k (M.op x y) y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq44590
       have r₂ := eq42947
       grind)
    | exact resolve eq44590 eq42947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42947 eq44590
  have eq45388 : (k (σ y) (σ y)) = (σ (k y (k y x))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq36 (k y x)
       have i₂ := eq134
       grind)
    | exact superpose eq134 eq36
    | exact resolve eq36 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq134
  have eq45433 : (M.op (σ y) (σ y)) = (σ (k y (k y x))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq45388
       have i₂ := eq100 sF3
       grind)
    | exact superpose eq100 eq45388
    | exact resolve eq45388 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45388
  have eq45864 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq39499 eq44659
    | exact resolve eq44659 eq39499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39499 eq44659
  have eq45926 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq45864
  have eq45958 : (σ (M.op x y)) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq45926
       have r₂ := eq42936
       grind)
    | exact resolve eq45926 eq42936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45926
  have eq45960 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45958
       have i₂ := eq100 y
       grind)
    | exact superpose eq100 eq45958
    | exact resolve eq45958 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45958
  have eq45962 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45960
       have i₂ := eq138 y
       grind)
    | exact superpose eq138 eq45960
    | exact resolve eq45960 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45960
  have eq45964 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45962
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq45962
    | exact resolve eq45962 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq45962
  have eq46043 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45964 eq743
    | exact resolve eq743 eq45964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743 eq45964
  have eq46055 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq46043
       have i₂ := eq100 sF1
       grind)
    | exact superpose eq100 eq46043
    | exact resolve eq46043 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq46043
  have eq46111 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq46055 eq23558
    | exact resolve eq23558 eq46055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23558 eq46055
  have eq46150 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq46111
  have eq46170 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq46150
    | exact resolve eq46150 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46150
  have eq46181 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq46170
       have r₂ := eq27
       grind)
    | exact resolve eq46170 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46170
  have eq46190 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq46181 eq39
    | exact resolve eq39 eq46181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq46181
  have eq46271 : x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq46190
    | exact resolve eq46190 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq46190
  have eq46275 : x = (M.op x y) := by
    first
    | (have r₁ := eq46271
       have r₂ := eq42936
       grind)
    | exact resolve eq46271 eq42936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42936 eq46271
  have eq46277 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq46275 eq20
    | exact resolve eq20 eq46275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq46284 : (k (σ y) (σ (M.op x y))) = (σ (k y x)) := by
    first
    | exact superpose eq46275 eq42
    | exact resolve eq42 eq46275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq46286 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq46275 eq80
    | exact resolve eq80 eq46275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq46343 : x = (k y (M.op x x)) := by
    first
    | exact superpose eq46275 eq742
    | exact resolve eq742 eq46275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq46275
  have eq53187 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq46277
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq46277
    | exact resolve eq46277 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46277
  have eq53776 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq53187 eq22
    | exact resolve eq22 eq53187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq53777 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq53187 eq26
    | exact resolve eq26 eq53187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq56060 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ y) (σ y)) = (σ (k y (k y x))) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq53187 eq45433
    | exact resolve eq45433 eq53187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45433
  have eq56910 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ y) (σ y)) = (σ (k y (k y x))) := by
    first
    | exact superpose eq53187 eq56060
    | exact resolve eq56060 eq53187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53187 eq56060
  have eq59061 : x = (M.op x x) := by
    first
    | (have i₁ := eq46286 (M.op x x)
       have i₂ := eq46286 x
       grind)
    | exact superpose eq46286 eq46286
    | exact resolve eq46286 eq46286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46286
  have eq59189 : x = (k y x) := by
    first
    | (have i₁ := eq46343
       have i₂ := eq59061
       grind)
    | exact superpose eq59061 eq46343
    | exact resolve eq46343 eq59061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46343
  have eq59551 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq46284
       have i₂ := eq59189
       grind)
    | exact superpose eq59189 eq46284
    | exact resolve eq46284 eq59189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46284
  have eq59652 : (σ (k y x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq56910
       have i₂ := eq59189
       grind)
    | exact superpose eq59189 eq56910
    | exact resolve eq56910 eq59189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56910
  have eq59711 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq59652
       have i₂ := eq59189
       grind)
    | exact superpose eq59189 eq59652
    | exact resolve eq59652 eq59189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59189 eq59652
  have eq59813 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq59551
       have i₂ := eq53776
       grind)
    | exact superpose eq53776 eq59551
    | exact resolve eq59551 eq53776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59551
  have eq59850 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq59711
       have i₂ := eq53776
       grind)
    | exact superpose eq53776 eq59711
    | exact resolve eq59711 eq53776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59711
  have eq60111 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq138 x
       have i₂ := eq59061
       grind)
    | exact superpose eq59061 eq138
    | exact resolve eq138 eq59061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq59061
  have eq60211 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq60111
       have i₂ := eq53776
       grind)
    | exact superpose eq53776 eq60111
    | exact resolve eq60111 eq53776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53776 eq60111
  have eq60912 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq60211 eq59850
    | exact resolve eq59850 eq60211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59850
  have eq60922 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq60912
  have eq60935 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq60211 eq60922
    | exact resolve eq60922 eq60211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60922
  have eq61132 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq60935
       have r₂ := eq27
       grind)
    | exact resolve eq60935 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60935
  have eq62932 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq61132 eq7206
    | exact resolve eq7206 eq61132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7206 eq61132
  have eq62953 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq59813 eq62932
    | exact resolve eq62932 eq59813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59813 eq62932
  have eq64233 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq62953 eq53777
    | exact resolve eq53777 eq62953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53777 eq62953
  have eq64884 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq60211 eq64233
    | exact resolve eq64233 eq60211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60211 eq64233
  have eq65320 : False := by grind
  exact eq65320

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = X then m(X,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_x_pyx_pxx_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq28 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 X0 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y X0
       grind)
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq29 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29
    | (have j0 := eq29 y
       grind)
    | exact resolve eq29 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq53 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq77 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq53 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 x y X0
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 (σ x) (σ y) X0
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq53 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 X0 x y
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq53 X2 X0 x
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq77 eq53
    | exact resolve eq53 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
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
  clear eq18
  have eq97 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq53 X0 X0 X0
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | exact superpose eq59 eq97
    | exact resolve eq97 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq121 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq130 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq59
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq59
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq130
    | exact resolve eq130 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq136 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq134
    | exact resolve eq134 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq139 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq100 (σ X0)
       grind)
    | exact superpose eq100 eq15
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq139 X0
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq139
    | exact resolve eq139 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq171 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq15
    | exact resolve eq15 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq215 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq140 X0
       grind)
    | exact superpose eq140 eq10
    | exact resolve eq10 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 : G, (σ (k (M.op x y) (M.op X0 X0))) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op X0 X0)
       have i₂ := eq140 X0
       grind)
    | exact superpose eq140 eq28
    | exact resolve eq28 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq223 : ∀ X0 : G, (σ (k y (M.op X0 X0))) = (k (σ y) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq36 (M.op X0 X0)
       have i₂ := eq140 X0
       grind)
    | exact superpose eq140 eq36
    | exact resolve eq36 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq215 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq215
    | exact resolve eq215 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq366 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ (k y x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq59 eq366
    | exact resolve eq366 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq366
  have eq1076 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq121 X0 X1
       grind)
    | exact superpose eq121 eq10
    | (have j1 := eq121 X0 X1
       grind)
    | exact resolve eq10 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq1103 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1076 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1076
    | (have j0 := eq1076 X0 X1
       grind)
    | exact resolve eq1076 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq1335 : (k (σ y) (σ y)) = (σ (k y (k y x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq36 (k y x)
       have i₂ := eq136
       grind)
    | exact superpose eq136 eq36
    | exact resolve eq36 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq136
  have eq1336 : (M.op (σ y) (σ y)) = (σ (k y (k y x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1335
       have i₂ := eq100 sF3
       grind)
    | exact superpose eq100 eq1335
    | exact resolve eq1335 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335
  have eq1369 : (σ (k (M.op x y) (M.op x x))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq218 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq218
    | (have j0 := eq218 x
       grind)
    | exact resolve eq218 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq1400 : (σ (M.op x y)) = (σ (k (M.op x y) (M.op x x))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq1369 eq14
    | (have j0 := eq14 (σ (M.op x y)) (M.op (σ x) (σ x))
       grind)
    | exact resolve eq14 eq1369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1401 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (k (M.op x y) (M.op x x))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1400
       have i₂ := eq53 sF2 sF2 sF2
       grind)
    | (have i₁ := eq1400
       have i₂ := eq53 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq53 eq1400
    | exact resolve eq1400 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400
  have eq2079 : (k (σ y) (M.op (σ y) (σ y))) = (σ (k y (M.op y y))) := by
    first
    | (have i₁ := eq223 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq223
    | (have j0 := eq223 y
       grind)
    | exact resolve eq223 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2080 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq223
    | (have j0 := eq223 (M.op x y)
       grind)
    | exact resolve eq223 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq2135 : (σ y) = (σ (k y (M.op (M.op x y) (M.op x y)))) ∨ (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq2080 eq14
    | (have j0 := eq14 (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq14 eq2080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2136 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (σ (k y (M.op (M.op x y) (M.op x y)))) ∨ (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq2135
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq2135
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq2135
    | exact resolve eq2135 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2135
  have eq2221 : ∀ X0 X1 : G, (k (σ X0) (k (σ y) X1)) = (σ (k X0 (k y (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq171 y X1 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq171
    | (have j0 := eq171 y X1 X0
       grind)
    | exact resolve eq171 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq3174 : ∀ X0 : G, (k (σ X0) (k (σ y) (σ y))) = (σ (k X0 (k y y))) := by
    intro X0
    first
    | exact superpose eq39 eq2221
    | exact resolve eq2221 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2221
  have eq3286 : ∀ X0 : G, (k (σ X0) (k (σ y) (σ y))) = (σ (k X0 (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq3174 X0
       have i₂ := eq100 y
       grind)
    | exact superpose eq100 eq3174
    | exact resolve eq3174 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3174
  have eq3326 : ∀ X0 : G, (k (σ X0) (M.op (σ y) (σ y))) = (σ (k X0 (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq3286 X0
       have i₂ := eq100 sF3
       grind)
    | exact superpose eq100 eq3286
    | exact resolve eq3286 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3286
  have eq5271 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq99 (M.op x X0) X0
       have i₂ := eq82 X0 (M.op x X0) x
       grind)
    | exact superpose eq82 eq99
    | (have r₁ := eq99 (M.op x X0) X0
       have r₂ := eq82 X0 (M.op x X0) x
       grind)
    | exact resolve eq99 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5273 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq83 eq99
    | (have r₁ := eq99 (M.op x y) y
       have r₂ := eq83 (M.op x y)
       grind)
    | exact resolve eq99 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq5274 : x ≠ x ∨ x = (k (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq80 eq99
    | (have r₁ := eq99 x (M.op x y)
       have r₂ := eq80 x
       grind)
    | exact resolve eq99 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq5280 : x = (k (M.op x y) (M.op x x)) := by grind
  clear eq5274
  have eq5281 : (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by grind
  clear eq5273
  have eq5283 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq5271 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5271
  have eq5285 : (σ x) = (σ (M.op x y)) ∨ (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq5280 eq1401
    | exact resolve eq1401 eq5280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401
  have eq5286 : (σ x) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5280 eq1369
    | exact resolve eq1369 eq5280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369
  have eq5288 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq5281 eq2136
    | exact resolve eq2136 eq5281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2136
  have eq5289 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq5281 eq2080
    | exact resolve eq2080 eq5281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2080 eq5281
  have eq5290 : (σ x) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq5286
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5286
    | exact resolve eq5286 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5286
  have eq5291 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq5285
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5285
    | exact resolve eq5285 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5285
  have eq5293 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq5289
    | exact resolve eq5289 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5289
  have eq5294 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq5288
    | exact resolve eq5288 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5288
  have eq26545 : x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x x)) (σ (M.op x y))) ∨ (M.op (σ (M.op x x)) (σ (M.op x y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq5280
       have i₂ := eq1103 sF0 (M.op x x)
       grind)
    | exact superpose eq1103 eq5280
    | (have j1 := eq1103 (M.op x y) (M.op x x)
       grind)
    | exact resolve eq5280 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103 eq5280
  have eq26892 : (σ (M.op x y)) = (M.op (σ (M.op x x)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op (σ (M.op x x)) (σ (M.op x y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | exact superpose eq20 eq26545
    | exact resolve eq26545 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26545
  have eq27138 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op (σ (M.op x x)) (σ (M.op x y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq26892
       have i₂ := eq140 x
       grind)
    | exact superpose eq140 eq26892
    | exact resolve eq26892 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26892
  have eq27284 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op (σ (M.op x x)) (σ (M.op x y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq27138
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27138
    | exact resolve eq27138 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27138
  have eq27391 : (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27284
       have i₂ := eq140 x
       grind)
    | exact superpose eq140 eq27284
    | exact resolve eq27284 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27284
  have eq27451 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27391
       have i₂ := eq53 (σ x) (σ x) (σ x)
       grind)
    | (have i₁ := eq27391
       have i₂ := eq53 x (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) x
       grind)
    | exact superpose eq53 eq27391
    | exact resolve eq27391 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27391
  have eq27506 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq27451
    | exact resolve eq27451 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27451
  have eq27551 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27506
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27506
    | exact resolve eq27506 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27506
  have eq76647 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq27551 eq53
    | exact resolve eq53 eq27551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27551
  have eq76846 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq5291 eq53
    | exact resolve eq53 eq5291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76865 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5294 eq54
    | exact resolve eq54 eq5294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq76868 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq5294 eq53
    | exact resolve eq53 eq5294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76873 : (σ y) = (k (σ y) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5294 eq5283
    | exact resolve eq5283 eq5294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5283 eq5294
  have eq76877 : (σ y) = (σ (k y (M.op y y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2079 eq76873
    | exact resolve eq76873 eq2079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2079 eq76873
  have eq81176 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq76868 eq78
    | exact resolve eq78 eq76868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq76868
  have eq81222 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq81176 eq53
    | exact resolve eq53 eq81176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81176
  have eq81239 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq81222 eq76846
    | exact resolve eq76846 eq81222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76846 eq81222
  have eq81275 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq81239
    | exact resolve eq81239 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81239
  have eq81279 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq81275
       have r₂ := eq27
       grind)
    | exact resolve eq81275 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81275
  have eq81341 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq81279 eq13
    | (have j0 := eq13 (σ (M.op x y)) (M.op (σ x) (σ x))
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (M.op (σ x) (σ x))
       have r₂ := eq81279
       grind)
    | (have r₁ := eq13 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq81279
       grind)
    | exact resolve eq13 eq81279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81343 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq81279 eq53
    | exact resolve eq53 eq81279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81279
  have eq81353 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq81341
  have eq81363 : (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq81353
       have i₂ := eq53 sF2 sF2 sF2
       grind)
    | (have i₁ := eq81353
       have i₂ := eq53 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq53 eq81353
    | exact resolve eq81353 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81353
  have eq81364 : (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq81363
  have eq81373 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5290 eq81364
    | exact resolve eq81364 eq5290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81364
  have eq81384 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq81373 eq53
    | exact resolve eq53 eq81373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81373
  have eq81822 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq81343 eq81343
    | exact resolve eq81343 eq81343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81343
  have eq81866 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq81822
  have eq81882 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq81866 eq53
    | exact resolve eq53 eq81866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81866
  have eq82083 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq81384 eq81384
    | exact resolve eq81384 eq81384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81384
  have eq82111 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq82083
  have eq82136 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq82111 eq261
    | exact resolve eq261 eq82111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82111
  have eq82180 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq39 eq82136
    | exact resolve eq82136 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82136
  have eq88757 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq81882 eq81882
    | exact resolve eq81882 eq81882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81882
  have eq88819 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq88757
  have eq88868 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq88819 eq261
    | exact resolve eq261 eq88819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq88819
  have eq88925 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq39 eq88868
    | exact resolve eq88868 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88868
  have eq88962 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq88925 eq82180
    | exact resolve eq82180 eq88925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82180 eq88925
  have eq89003 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq88962
  have eq89461 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq140 y
       have i₂ := eq89003
       grind)
    | exact superpose eq89003 eq140
    | exact resolve eq140 eq89003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89003
  have eq89516 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq89461
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq89461
    | exact resolve eq89461 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89461
  have eq89623 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq89516 eq82
    | exact resolve eq82 eq89516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq89516
  have eq90041 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq76865 eq89623
    | exact resolve eq89623 eq76865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76865
  have eq90132 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq90041
  have eq115908 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq90132 eq89623
    | exact resolve eq89623 eq90132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90132
  have eq115925 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq115908
  have eq127973 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq115925 eq13
    | (have j0 := eq13 (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | (have r₁ := eq13 (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))
       have r₂ := eq115925
       grind)
    | (have r₁ := eq13 (σ y) (σ (M.op x y))
       have r₂ := eq115925
       grind)
    | exact resolve eq13 eq115925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115925
  have eq127986 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq127973
  have eq128020 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq127986
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq127986
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq127986
    | exact resolve eq127986 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127986
  have eq128021 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq128020
  have eq128030 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq5293 eq128021
    | exact resolve eq128021 eq5293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128021
  have eq128123 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq128030 eq89623
    | exact resolve eq89623 eq128030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89623 eq128030
  have eq128156 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq128123
  have eq128269 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq128156 eq53
    | exact resolve eq53 eq128156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128324 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq5291 eq128269
    | exact resolve eq128269 eq5291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5291
  have eq128395 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) := by grind
  clear eq128324
  have eq128408 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq128395
    | exact resolve eq128395 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128395
  have eq128413 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq128408
       have r₂ := eq27
       grind)
    | exact resolve eq128408 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128408
  have eq128835 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq128413 eq128269
    | exact resolve eq128269 eq128413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128269 eq128413
  have eq128850 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq128835
  have eq128892 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq128850 eq128156
    | exact resolve eq128156 eq128850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128156 eq128850
  have eq128946 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq128892
  have eq128962 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq128946 eq39
    | exact resolve eq39 eq128946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq128946
  have eq129041 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq128962
    | exact resolve eq128962 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128962
  have eq129049 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq129041 eq38
    | exact resolve eq38 eq129041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129041
  have eq129138 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq129049
    | exact resolve eq129049 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129049
  have eq129142 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129138 eq20
    | exact resolve eq20 eq129138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129143 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq129138 eq77
    | exact resolve eq77 eq129138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq129271 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq129290 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq129142
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq129142
    | exact resolve eq129142 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129142
  have eq130001 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq129143 (M.op y x)
       have i₂ := eq129143 x
       grind)
    | exact superpose eq129143 eq129143
    | exact resolve eq129143 eq129143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129143
  have eq130054 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq130001
  have eq130181 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq140 y
       have i₂ := eq130054
       grind)
    | exact superpose eq130054 eq140
    | exact resolve eq140 eq130054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130054
  have eq130235 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq130181
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq130181
    | exact resolve eq130181 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130181
  have eq130250 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129290 eq130235
    | exact resolve eq130235 eq129290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129290 eq130235
  have eq130366 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq130250
  have eq130443 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq130366 eq5293
    | exact resolve eq5293 eq130366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5293
  have eq130538 : (σ (M.op x y)) = (σ (k y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42 eq130443
    | exact resolve eq130443 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq130443
  have eq130955 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq129138 eq130538
    | exact resolve eq130538 eq129138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129138 eq130538
  have eq131067 : (σ (M.op x y)) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq130955
       have r₂ := eq129271
       grind)
    | exact resolve eq130955 eq129271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129271 eq130955
  have eq131072 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq131067
       have i₂ := eq100 y
       grind)
    | exact superpose eq100 eq131067
    | exact resolve eq131067 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq131067
  have eq131075 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq131072
       have i₂ := eq140 y
       grind)
    | exact superpose eq140 eq131072
    | exact resolve eq131072 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131072
  have eq131077 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq131075
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq131075
    | exact resolve eq131075 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq131075
  have eq131190 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq131077 eq53
    | exact resolve eq53 eq131077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131077
  have eq134704 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq131190 eq76647
    | exact resolve eq76647 eq131190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76647 eq131190
  have eq134739 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq134704
  have eq134759 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq134739
    | exact resolve eq134739 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134739
  have eq134765 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq134759
       have r₂ := eq27
       grind)
    | exact resolve eq134759 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134759
  have eq135659 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq134765 eq13
    | (have j0 := eq13 (σ (M.op x y)) (M.op (σ x) (σ x))
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (M.op (σ x) (σ x))
       have r₂ := eq134765
       grind)
    | exact resolve eq13 eq134765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134765
  have eq135672 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq135659
  have eq135692 : (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq135672
       have i₂ := eq53 sF2 sF2 sF2
       grind)
    | (have i₁ := eq135672
       have i₂ := eq53 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq53 eq135672
    | exact resolve eq135672 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq135672
  have eq135702 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5290 eq135692
    | exact resolve eq135692 eq5290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5290 eq135692
  have eq150407 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq135702 eq130366
    | exact resolve eq130366 eq135702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130366 eq135702
  have eq150509 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq150407
  have eq150555 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq150509 eq38
    | exact resolve eq38 eq150509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq150509
  have eq150681 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq150555
    | exact resolve eq150555 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq150555
  have eq150682 : x = (M.op x y) := by grind
  clear eq150681
  have eq150687 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq150682 eq20
    | exact resolve eq20 eq150682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq150689 : ∀ X0 : G, (k (σ X0) (σ (M.op x y))) = (σ (k X0 x)) := by
    intro X0
    first
    | exact superpose eq150682 eq29
    | exact resolve eq29 eq150682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq150696 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq150682 eq80
    | exact resolve eq80 eq150682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq150699 : x ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq150682 eq95
    | exact resolve eq95 eq150682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq166496 : x = (k y x) ∨ x ≠ (M.op x x) := by
    first
    | exact superpose eq150682 eq150699
    | exact resolve eq150699 eq150682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150682 eq150699
  have eq166504 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq150687
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq150687
    | exact resolve eq150687 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150687
  have eq166944 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq166504 eq22
    | exact resolve eq22 eq166504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq166945 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq166504 eq26
    | exact resolve eq26 eq166504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq166953 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | exact superpose eq166504 eq104
    | exact resolve eq104 eq166504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq166965 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ (k y x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq166504 eq369
    | exact resolve eq369 eq166504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq167043 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ y) (σ y)) = (σ (k y (k y x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq166504 eq1336
    | exact resolve eq1336 eq166504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336 eq166504
  have eq172295 : x = (M.op x x) := by
    first
    | (have i₁ := eq150696 (M.op x x)
       have i₂ := eq150696 x
       grind)
    | exact superpose eq150696 eq150696
    | exact resolve eq150696 eq150696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150696
  have eq172521 : x ≠ x ∨ x = (k y x) := by
    first
    | (have i₁ := eq166496
       have i₂ := eq172295
       grind)
    | exact superpose eq172295 eq166496
    | (have r₁ := eq166496
       have r₂ := eq172295
       grind)
    | exact resolve eq166496 eq172295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166496
  have eq172560 : x = (k y x) := by grind
  clear eq172521
  have eq172605 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq166953
       have i₂ := eq172560
       grind)
    | exact superpose eq172560 eq166953
    | exact resolve eq166953 eq172560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166953
  have eq172607 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq166965
       have i₂ := eq172560
       grind)
    | exact superpose eq172560 eq166965
    | exact resolve eq166965 eq172560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166965
  have eq172608 : (σ (k y x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq167043
       have i₂ := eq172560
       grind)
    | exact superpose eq172560 eq167043
    | exact resolve eq167043 eq172560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167043
  have eq172667 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq172608
       have i₂ := eq172560
       grind)
    | exact superpose eq172560 eq172608
    | exact resolve eq172608 eq172560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172608
  have eq172668 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq172607
       have i₂ := eq166944
       grind)
    | exact superpose eq166944 eq172607
    | exact resolve eq172607 eq166944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172607
  have eq172670 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq172605
       have i₂ := eq166944
       grind)
    | exact superpose eq166944 eq172605
    | exact resolve eq172605 eq166944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172605
  have eq172695 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq172667
       have i₂ := eq166944
       grind)
    | exact superpose eq166944 eq172667
    | exact resolve eq172667 eq166944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172667
  have eq172696 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq172670
       have r₂ := eq27
       grind)
    | exact resolve eq172670 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172670
  have eq172701 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq172695
       have r₂ := eq172668
       grind)
    | exact resolve eq172695 eq172668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172668 eq172695
  have eq172703 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq172701
       have r₂ := eq172696
       grind)
    | exact resolve eq172701 eq172696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172696 eq172701
  have eq172714 : ∀ X0 : G, (k (σ X0) (σ (M.op x y))) = (σ (k X0 (M.op y y))) := by
    intro X0
    first
    | exact superpose eq172703 eq3326
    | exact resolve eq3326 eq172703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3326 eq172703
  have eq173060 : ∀ X0 : G, (σ (k X0 x)) = (σ (k X0 (M.op y y))) := by
    intro X0
    first
    | exact superpose eq150689 eq172714
    | exact resolve eq172714 eq150689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150689 eq172714
  have eq173256 : (σ y) = (σ (k y x)) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq76877
       have i₂ := eq173060 y
       grind)
    | exact superpose eq173060 eq76877
    | exact resolve eq76877 eq173060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76877 eq173060
  have eq173307 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq173256
       have i₂ := eq172560
       grind)
    | exact superpose eq172560 eq173256
    | exact resolve eq173256 eq172560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172560 eq173256
  have eq173354 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq173307
       have i₂ := eq166944
       grind)
    | exact superpose eq166944 eq173307
    | exact resolve eq173307 eq166944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173307
  have eq173355 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by grind
  clear eq173354
  have eq173529 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq140 x
       have i₂ := eq172295
       grind)
    | exact superpose eq172295 eq140
    | exact resolve eq140 eq172295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq172295
  have eq173645 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq173529
       have i₂ := eq166944
       grind)
    | exact superpose eq166944 eq173529
    | exact resolve eq173529 eq166944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166944 eq173529
  have eq173922 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq173645 eq173355
    | exact resolve eq173355 eq173645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173355
  have eq173940 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq166945 eq173922
    | exact resolve eq173922 eq166945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173922
  have eq174012 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq173940
       have r₂ := eq27
       grind)
    | exact resolve eq173940 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173940
  have eq180402 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq174012 eq166945
    | exact resolve eq166945 eq174012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166945 eq174012
  have eq183643 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq173645 eq180402
    | exact resolve eq180402 eq173645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173645 eq180402
  have eq184325 : False := by grind
  exact eq184325

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,Y) = X then m(Y,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_x_pyx_pyy_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b = a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
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
  have eq25 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq25 X2 X0 x
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq52 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq86 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq25 X0 X0 X0
       grind)
    | exact superpose eq25 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X2)) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X0 X1 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq25 X1 X1 x
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq25
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq25 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X1 ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X0 X0
       have i₂ := eq14 X1 (M.op X0 X0)
       grind)
    | (have i₁ := eq25 X0 x x
       have i₂ := eq14 (M.op x x) (M.op X0 x)
       grind)
    | exact superpose eq14 eq25
    | (have j1 := eq14 X1 (M.op X0 X0)
       grind)
    | exact resolve eq25 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 ∨ (M.op (M.op X0 X0) X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq119 X0 X1
       have i₂ := eq25 X0 X0 X0
       grind)
    | (have i₁ := eq119 X0 X1
       have i₂ := eq25 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq25 eq119
    | (have j0 := eq119 X0 X1
       grind)
    | exact resolve eq119 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq129 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq87 X0
       grind)
    | exact superpose eq87 eq15
    | exact resolve eq15 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq129 X0
       have i₂ := eq87 (σ X0)
       grind)
    | exact superpose eq87 eq129
    | exact resolve eq129 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq129
  have eq221 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) = (k X1 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq86 (M.op X0 X1) X1
       have i₂ := eq33 X1 (M.op X0 X1) X0
       grind)
    | exact superpose eq33 eq86
    | (have j0 := eq86 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq86 (M.op x X0) X0
       have r₂ := eq33 X0 (M.op x X0) x
       grind)
    | exact resolve eq86 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op (M.op X0 X0) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 (M.op X0 X1)
       have i₂ := eq25 X0 X0 X1
       grind)
    | exact superpose eq25 eq86
    | (have j0 := eq86 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq86 x (M.op x x)
       have r₂ := eq25 x x x
       grind)
    | exact resolve eq86 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq224 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq222 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq225 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) = (k X1 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq221 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq227 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq224 X0 X1
       have i₂ := eq25 X0 X0 X1
       grind)
    | (have i₁ := eq224 X0 X1
       have i₂ := eq25 X0 (M.op (M.op X0 X0) (M.op X0 X1)) x
       grind)
    | exact superpose eq25 eq224
    | exact resolve eq224 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq228 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq225 X0 X1
       have i₂ := eq33 X1 (M.op X0 X1) X0
       grind)
    | exact superpose eq33 eq225
    | exact resolve eq225 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq243 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 X1)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (M.op X0 X1) (M.op X0 X0)
       have i₂ := eq227 X0 X1
       grind)
    | exact superpose eq227 eq15
    | exact resolve eq15 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq247 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 X1)) (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq243 X0 X1
       have i₂ := eq130 X0
       grind)
    | exact superpose eq130 eq243
    | exact resolve eq243 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq300 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (k (σ X1) (σ (M.op (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq228 X0 X1
       grind)
    | exact superpose eq228 eq15
    | exact resolve eq15 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq303 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (k (σ X1) (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq300 X0 X1
       have i₂ := eq130 (M.op X0 X1)
       grind)
    | exact superpose eq130 eq300
    | exact resolve eq300 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq312 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) X1)) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq247 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq247
    | exact resolve eq247 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq344 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = X0 ∨ (M.op (M.op X0 X0) (σ (M.op (τ X0) X1))) = X0 ∨ (σ (M.op (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq124 X0 (σ (M.op (τ X0) X1))
       have i₂ := eq312 X0 X1
       grind)
    | exact superpose eq312 eq124
    | (have j0 := eq124 X0 (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq124 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq312
  have eq348 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = X0 ∨ (M.op (M.op X0 X0) (σ (M.op (τ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq344 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq737 : ∀ X0 X1 : G, (σ (M.op X1 (τ X0))) = (k X0 (M.op (σ (M.op X1 (τ X0))) (σ (M.op X1 (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq303 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq303
    | exact resolve eq303 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1558 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ (M.op (τ X0) X1))) = X0 ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) X1)
       have i₂ := eq348 X0 X1
       grind)
    | exact superpose eq348 eq10
    | (have j1 := eq348 X0 X1
       grind)
    | exact resolve eq10 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq1836 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (σ (M.op (τ X0) X1))) = X0 ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 (σ (M.op (τ X0) X1)) X1 (M.op X0 X0)
       have i₂ := eq1558 X0 X1
       grind)
    | exact superpose eq1558 eq33
    | (have j1 := eq1558 X0 X1
       grind)
    | exact resolve eq33 eq1558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1558
  have eq1883 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = X1 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X1 ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq107 (M.op X0 X0) X1 X2
       have i₂ := eq25 X0 X0 X0
       grind)
    | exact superpose eq25 eq107
    | (have j0 := eq107 (M.op X0 X0) X1 X2
       grind)
    | exact resolve eq107 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq1991 : ∀ X0 X1 X2 : G, (k X1 (M.op X0 X0)) = X1 ∨ (M.op X0 (M.op X1 X2)) = X1 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1883 X0 X1 X2
       have i₂ := eq25 X0 X0 X0
       grind)
    | (have i₁ := eq1883 X0 X1 X2
       have i₂ := eq25 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq25 eq1883
    | (have j0 := eq1883 X0 X1 X2
       grind)
    | exact resolve eq1883 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1883
  have eq2392 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X2))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1836 (σ X0) X2 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1836
    | (have j0 := eq1836 (σ X0) X2 X2
       grind)
    | exact resolve eq1836 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836
  have eq2467 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X2))) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2392 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2392
    | (have j0 := eq2392 X0 X1 X2
       grind)
    | exact resolve eq2392 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2392
  have eq2519 : ∀ X0 X2 X3 : G, (σ (M.op X0 X2)) = (M.op (σ X0) (M.op (σ (M.op X0 X2)) X3)) ∨ (M.op X0 X2) = X0 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq25 (M.op x (σ X0)) (σ (M.op X0 X2)) X3
       have i₂ := eq2467 X0 x X2
       grind)
    | exact superpose eq2467 eq25
    | (have j1 := eq2467 X0 x X2
       grind)
    | exact resolve eq25 eq2467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2467
  have eq3195 : ∀ X0 X1 X2 : G, (σ (M.op X0 (τ X1))) = X1 ∨ (M.op (σ (M.op X0 (τ X1))) (M.op X1 X2)) = X1 ∨ (σ (M.op X0 (τ X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1991 (σ (M.op X0 (τ X1))) X1 X2
       have i₂ := eq737 X1 X0
       grind)
    | exact superpose eq737 eq1991
    | (have j0 := eq1991 (σ (M.op X0 (τ X1))) X1 X2
       grind)
    | exact resolve eq1991 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737 eq1991
  have eq3203 : ∀ X0 X1 X2 : G, (σ (M.op X0 (τ X1))) = X1 ∨ (M.op (σ (M.op X0 (τ X1))) (M.op X1 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq3195 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3195
  have eq3279 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X1 (τ X0))) (M.op X0 X2)) = X0 ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X1 (τ X0))
       have i₂ := eq3203 X1 X0 X2
       grind)
    | exact superpose eq3203 eq10
    | (have j1 := eq3203 X1 X0 X2
       grind)
    | exact resolve eq10 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3203
  have eq3389 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (M.op X1 X0)) (M.op (σ X0) X2)) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3279 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3279
    | (have j0 := eq3279 (σ X0) X1 X2
       grind)
    | exact resolve eq3279 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3279
  have eq3502 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (M.op X1 X0)) (M.op (σ X0) X2)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3389 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3389
    | (have j0 := eq3389 X0 X1 X2
       grind)
    | exact resolve eq3389 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3389
  have eq5885 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2519 X1 X0 (M.op (σ X0) x)
       have i₂ := eq3502 X0 X1 x
       grind)
    | exact superpose eq3502 eq2519
    | (have j0 := eq2519 X1 X0 x
       have j1 := eq3502 X0 X1 x
       grind)
    | exact resolve eq2519 eq3502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2519
  have eq8799 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5885 y x
       grind)
    | exact superpose eq5885 eq16
    | (have j1 := eq5885 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq5885 y x
       grind)
    | exact resolve eq16 eq5885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5885
  have eq8843 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq8799
  have eq8943 : y ≠ (M.op x x) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq8843
       grind)
    | exact superpose eq8843 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq8843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8945 : ∀ X0 : G, x = (M.op x y) ∨ x = (M.op (M.op X0 x) y) := by
    intro X0
    first
    | (have i₁ := eq25 X0 x y
       have i₂ := eq8843
       grind)
    | exact superpose eq8843 eq25
    | exact resolve eq25 eq8843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8946 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq25 x y X0
       have i₂ := eq8843
       grind)
    | exact superpose eq8843 eq25
    | exact resolve eq25 eq8843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8956 : y ≠ y ∨ y = (M.op x x) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq121 x y
       have i₂ := eq8843
       grind)
    | exact superpose eq8843 eq121
    | (have j0 := eq121 x y
       grind)
    | (have r₁ := eq121 x y
       have r₂ := eq8843
       grind)
    | exact resolve eq121 eq8843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq8992 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq8843
  have eq9001 : y = (k y x) ∨ y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq8956
  have eq9046 : ∀ X0 X1 : G, x = (M.op (M.op X0 x) y) ∨ x = (M.op (M.op X1 x) y) := by
    intro X0 X1
    first
    | (have i₁ := eq33 y X1 x
       have i₂ := eq8945 X0
       grind)
    | exact superpose eq8945 eq33
    | (have j1 := eq8945 X0
       grind)
    | exact resolve eq33 eq8945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq8945
  have eq9109 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8946 (M.op y x)
       have i₂ := eq8946 x
       grind)
    | exact superpose eq8946 eq8946
    | exact resolve eq8946 eq8946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8946
  have eq9161 : x = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq9109
  have eq9191 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq25 X0 x y
       have i₂ := eq9161
       grind)
    | exact superpose eq9161 eq25
    | exact resolve eq25 eq9161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9161
  have eq9426 : x = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9191 (M.op x x)
       have i₂ := eq9191 x
       grind)
    | exact superpose eq9191 eq9191
    | exact resolve eq9191 eq9191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9191
  have eq9485 : x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq9426
  have eq9510 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq130 x
       have i₂ := eq9485
       grind)
    | exact superpose eq9485 eq130
    | exact resolve eq130 eq9485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9485
  have eq9952 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq130 y
       have i₂ := eq9510
       grind)
    | exact superpose eq9510 eq130
    | exact resolve eq130 eq9510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10464 : ∀ X0 : G, x ≠ x ∨ x = (M.op (M.op X0 x) y) := by
    intro X0
    first
    | (have j0 := eq9046 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9046
  have eq10465 : ∀ X0 : G, x = (M.op (M.op X0 x) y) := by
    intro X0
    first
    | (have j0 := eq10464 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10464
  have eq10537 : ∀ X1 : G, y = (M.op x (M.op y X1)) := by
    intro X1
    first
    | (have i₁ := eq25 (M.op x x) y X1
       have i₂ := eq10465 x
       grind)
    | exact superpose eq10465 eq25
    | exact resolve eq25 eq10465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq10559 : (σ x) = (k (σ y) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq303 (M.op x x) y
       have i₂ := eq10465 x
       grind)
    | exact superpose eq10465 eq303
    | exact resolve eq303 eq10465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq10579 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (M.op (σ y) X1)) ∨ y = (M.op (M.op X0 x) y) := by
    intro X0 X1
    first
    | (have i₁ := eq3502 y (M.op X0 x) X1
       have i₂ := eq10465 X0
       grind)
    | exact superpose eq10465 eq3502
    | (have j0 := eq3502 y (M.op X0 x) x
       grind)
    | exact resolve eq3502 eq10465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3502
  have eq10587 : ∀ X1 : G, x = y ∨ (σ y) = (M.op (σ x) (M.op (σ y) X1)) := by
    intro X1
    first
    | (have i₁ := eq10579 x X1
       have i₂ := eq10465 x
       grind)
    | exact superpose eq10465 eq10579
    | (have j0 := eq10579 x X1
       grind)
    | exact resolve eq10579 eq10465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10465 eq10579
  have eq10651 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10537 y
       have i₂ := eq9510
       grind)
    | exact superpose eq9510 eq10537
    | exact resolve eq10537 eq9510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9510 eq10537
  have eq11129 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq10587 x
       grind)
    | exact superpose eq10587 eq16
    | (have j1 := eq10587 X0
       grind)
    | exact resolve eq16 eq10587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10587
  have eq11159 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have j0 := eq11129 X0
       grind)
    | (have r₁ := eq11129 X0
       have r₂ := eq130 x
       grind)
    | exact resolve eq11129 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq11129
  have eq11487 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10651
       grind)
    | exact superpose eq10651 eq16
    | exact resolve eq16 eq10651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10651
  have eq14160 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11159 (σ y)
       have i₂ := eq9952
       grind)
    | exact superpose eq9952 eq11159
    | exact resolve eq11159 eq9952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9952 eq11159
  have eq14316 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq14160
       have r₂ := eq11487
       grind)
    | exact resolve eq14160 eq11487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11487 eq14160
  have eq14341 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq10559
       have i₂ := eq14316
       grind)
    | exact superpose eq14316 eq10559
    | exact resolve eq10559 eq14316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10559
  have eq14529 : (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq52 (σ x) (σ y)
       have i₂ := eq14341
       grind)
    | exact superpose eq14341 eq52
    | exact resolve eq52 eq14341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq14540 : x = (k (τ (σ y)) x) := by
    first
    | (have i₁ := eq14529
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq14529
    | exact resolve eq14529 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14529
  have eq14560 : x = (k y x) := by
    first
    | (have i₁ := eq14540
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq14540
    | exact resolve eq14540 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14540
  have eq14567 : x = (M.op x y) ∨ y ≠ (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8943
       have i₂ := eq14560
       grind)
    | exact superpose eq14560 eq8943
    | exact resolve eq8943 eq14560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8943
  have eq14573 : x = y ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9001
       have i₂ := eq14560
       grind)
    | exact superpose eq14560 eq9001
    | exact resolve eq9001 eq14560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9001 eq14560
  have eq14612 : x = (M.op x y) ∨ y ≠ (M.op x x) := by grind
  clear eq14567
  have eq14615 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14573
       have r₂ := eq8992
       grind)
    | exact resolve eq14573 eq8992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8992 eq14573
  have eq14624 : x = (M.op x y) := by
    first
    | (have r₁ := eq14615
       have r₂ := eq14612
       grind)
    | exact resolve eq14615 eq14612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14612 eq14615
  have eq14628 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14624
       grind)
    | exact superpose eq14624 eq16
    | exact resolve eq16 eq14624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14624
  have eq15649 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq14628
       have i₂ := eq14 (σ y) (σ x)
       grind)
    | exact superpose eq14 eq14628
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14628 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15650 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq15649
       have r₂ := eq14316
       grind)
    | exact resolve eq15649 eq14316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15649
  have eq15651 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq15650
       have i₂ := eq14316
       grind)
    | exact superpose eq14316 eq15650
    | exact resolve eq15650 eq14316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15650
  have eq15652 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq15651
       have i₂ := eq14341
       grind)
    | exact superpose eq14341 eq15651
    | exact resolve eq15651 eq14341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14341 eq15651
  have eq15653 : (σ x) = (σ y) := by grind
  clear eq15652
  have eq15800 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14628
       have i₂ := eq15653
       grind)
    | exact superpose eq15653 eq14628
    | exact resolve eq14628 eq15653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14628 eq15653
  have eq15844 : False := by grind
  exact eq15844

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pyy_pyx_pxy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
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
  clear eq22
  have eq61 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq61 X2 X0 x
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq365 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq365 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq365 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq377 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq366 (σ X0)
       grind)
    | exact superpose eq366 eq15
    | exact resolve eq15 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq366 (τ X0)
       grind)
    | exact superpose eq366 eq31
    | exact resolve eq31 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq390 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq383 X0
       have i₂ := eq366 X0
       grind)
    | exact superpose eq366 eq383
    | exact resolve eq383 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq396 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq377 X0
       have i₂ := eq366 X0
       grind)
    | exact superpose eq366 eq377
    | exact resolve eq377 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366 eq377
  have eq633 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq658 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq633 X0 X1
       have i₂ := eq396 X1
       grind)
    | exact superpose eq396 eq633
    | (have j0 := eq633 X0 X1
       grind)
    | exact resolve eq633 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq672 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq658 X0 X1
       have i₂ := eq396 X0
       grind)
    | exact superpose eq396 eq658
    | (have j0 := eq658 X0 X1
       grind)
    | exact resolve eq658 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq2606 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq672 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq672
    | (have j0 := eq672 (τ X0) X1
       grind)
    | exact resolve eq672 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq2667 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2606 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq2606
    | (have j0 := eq2606 X0 X1
       grind)
    | exact resolve eq2606 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2606
  have eq2684 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2667 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq2667 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq2667 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2667
  have eq2686 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (σ (M.op X1 X1)) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2684 X0 X1
       have i₂ := eq390 X0
       grind)
    | exact superpose eq390 eq2684
    | (have j0 := eq2684 X0 X1
       grind)
    | exact resolve eq2684 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2684
  have eq2688 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2686 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq2686
    | (have j0 := eq2686 X0 X1
       grind)
    | exact resolve eq2686 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2686
  have eq2690 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2688 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2688
    | (have j0 := eq2688 X1 (τ X0)
       grind)
    | exact resolve eq2688 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2710 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq2688 (σ X1) X0
       grind)
    | exact superpose eq2688 eq15
    | (have j1 := eq2688 (σ X1) X0
       grind)
    | exact resolve eq15 eq2688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2688
  have eq2747 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2710 X0 X1
       have i₂ := eq396 X1
       grind)
    | exact superpose eq396 eq2710
    | (have j0 := eq2710 X0 X1
       grind)
    | exact resolve eq2710 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2710
  have eq2760 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2690 X0 X1
       have i₂ := eq390 X0
       grind)
    | exact superpose eq390 eq2690
    | (have j0 := eq2690 X0 X1
       grind)
    | exact resolve eq2690 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2690
  have eq2766 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2760 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq2760
    | (have j0 := eq2760 X0 X1
       grind)
    | exact resolve eq2760 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2760
  have eq2798 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq2766 X0 (τ X1)
       grind)
    | exact superpose eq2766 eq17
    | (have j1 := eq2766 X0 (τ X1)
       grind)
    | exact resolve eq17 eq2766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq2766
  have eq2839 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2798 X0 X1
       have i₂ := eq390 X1
       grind)
    | exact superpose eq390 eq2798
    | (have j0 := eq2798 X0 X1
       grind)
    | exact resolve eq2798 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390 eq2798
  have eq3140 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2839 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2839
    | (have j0 := eq2839 X1 (σ X0)
       grind)
    | exact resolve eq2839 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2839
  have eq3218 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3140 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3140
    | (have j0 := eq3140 X0 X1
       grind)
    | exact resolve eq3140 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3140
  have eq3225 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3218 X0 X1
       have i₂ := eq396 X0
       grind)
    | exact superpose eq396 eq3218
    | (have j0 := eq3218 X0 X1
       grind)
    | exact resolve eq3218 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3218
  have eq3228 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3225 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq3225
    | (have j0 := eq3225 X0 X1
       grind)
    | exact resolve eq3225 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3225
  have eq3702 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2747 x y
       grind)
    | exact superpose eq2747 eq16
    | (have j1 := eq2747 x y
       grind)
    | exact resolve eq16 eq2747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2747
  have eq3777 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq3702
       have i₂ := eq3228 y x
       grind)
    | exact superpose eq3228 eq3702
    | (have j1 := eq3228 x y
       grind)
    | (have r₁ := eq3702
       have r₂ := eq3228 y x
       grind)
    | exact resolve eq3702 eq3228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3228 eq3702
  have eq3778 : (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq3777
  have eq3810 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq61 X0 y y
       have i₂ := eq3778
       grind)
    | exact superpose eq3778 eq61
    | exact resolve eq61 eq3778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3811 : ∀ X0 : G, y = (M.op (M.op x x) (M.op y X0)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq61 y y X0
       have i₂ := eq3778
       grind)
    | exact superpose eq3778 eq61
    | exact resolve eq61 eq3778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3778
  have eq3831 : (M.op x x) = (M.op y x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq67 x (M.op x y) x
       have i₂ := eq3810 x
       grind)
    | exact superpose eq3810 eq67
    | exact resolve eq67 eq3810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq3810
  have eq3865 : y = (M.op (M.op x x) (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3811 x
       have i₂ := eq3831
       grind)
    | exact superpose eq3831 eq3811
    | exact resolve eq3811 eq3831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3811 eq3831
  have eq3886 : y = (M.op (M.op x x) (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq3865
  have eq3887 : x = y ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3886
       have i₂ := eq61 x x x
       grind)
    | (have i₁ := eq3886
       have i₂ := eq61 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq61 eq3886
    | exact resolve eq3886 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3886
  have eq3888 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3887
       grind)
    | exact superpose eq3887 eq16
    | exact resolve eq16 eq3887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3887
  have eq3889 : (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq3888
       have r₂ := eq396 x
       grind)
    | exact resolve eq3888 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3888
  have eq3919 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq396 (M.op y y)
       have i₂ := eq3889
       grind)
    | exact superpose eq3889 eq396
    | exact resolve eq396 eq3889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3889
  have eq3960 : (σ (M.op (M.op y y) (M.op y y))) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq3919
       have i₂ := eq396 (M.op x x)
       grind)
    | exact superpose eq396 eq3919
    | exact resolve eq3919 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3919
  have eq3978 : (σ x) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq3960
       have i₂ := eq61 x x x
       grind)
    | (have i₁ := eq3960
       have i₂ := eq61 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq61 eq3960
    | exact resolve eq3960 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3960
  have eq3979 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3978
       have i₂ := eq61 y y y
       grind)
    | (have i₁ := eq3978
       have i₂ := eq61 x (M.op (M.op y y) (M.op y y)) x
       grind)
    | exact superpose eq61 eq3978
    | exact resolve eq3978 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq3978
  have eq3980 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3979
       grind)
    | exact superpose eq3979 eq16
    | exact resolve eq16 eq3979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3981 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3979
       grind)
    | exact superpose eq3979 eq10
    | exact resolve eq10 eq3979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3979
  have eq4056 : x = y := by
    first
    | (have i₁ := eq3981
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3981
    | exact resolve eq3981 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3981
  have eq4057 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq3980
       have i₂ := eq396 x
       grind)
    | exact superpose eq396 eq3980
    | exact resolve eq3980 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396 eq3980
  have eq4058 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4057
       have i₂ := eq4056
       grind)
    | exact superpose eq4056 eq4057
    | exact resolve eq4057 eq4056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4056 eq4057
  have eq4059 : False := by grind
  exact eq4059

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_pyy_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
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
  have eq50 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq14 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq14 X0 x x X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq76 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq77 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq98 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq110 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (M.op X1 X2) = X1 ∨ (M.op X2 X2) = (k X2 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq11 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq11 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq12 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X2) = X1 ∨ (M.op X0 X0) = (k X2 X1) ∨ (M.op X0 X2) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq11 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq11 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq11 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq12 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq115 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq115 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq115 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq119 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq116 x
       grind)
    | exact superpose eq116 eq43
    | exact resolve eq43 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq120 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq116 y
       grind)
    | exact superpose eq116 eq76
    | exact resolve eq76 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq121 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq116 sF2
       grind)
    | exact superpose eq116 eq49
    | exact resolve eq49 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq122 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq121
       have i₂ := eq116 x
       grind)
    | exact superpose eq116 eq121
    | exact resolve eq121 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq123 : (σ (M.op y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq120
       have i₂ := eq116 sF3
       grind)
    | exact superpose eq116 eq120
    | exact resolve eq120 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq124 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq119
       have i₂ := eq116 sF2
       grind)
    | exact superpose eq116 eq119
    | exact resolve eq119 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq260 : (σ x) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq50
    | (have j0 := eq50 (σ x) (σ y)
       grind)
    | exact resolve eq50 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq330 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X2)) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 X1 X2
       have i₂ := eq11 X0 X1
       grind)
    | (have i₁ := eq52 X0 X0 x
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq52
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq52 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq341 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ x) (σ y) X0
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 X0)) = X2 ∨ (M.op X0 X2) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 X2 X2
       have i₂ := eq11 X2 X0
       grind)
    | (have i₁ := eq52 X0 X1 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq52
    | (have j1 := eq11 X2 X0
       grind)
    | exact resolve eq52 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 X0 x y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 (σ x) (σ y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq388 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq341 eq51
    | exact resolve eq51 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq465 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq116 (τ X0)
       grind)
    | exact superpose eq116 eq34
    | exact resolve eq34 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq475 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq465 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq465
    | exact resolve eq465 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq477 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq475 X0
       have i₂ := eq116 X0
       grind)
    | exact superpose eq116 eq475
    | exact resolve eq475 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq475
  have eq522 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1002 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq477 X0
       grind)
    | exact superpose eq477 eq16
    | exact resolve eq16 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq1039 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq522 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq522
    | (have j0 := eq522 y X0
       grind)
    | exact resolve eq522 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq1389 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (τ X0) (τ X0) X1
       have i₂ := eq1002 X0
       grind)
    | exact superpose eq1002 eq52
    | exact resolve eq52 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1815 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq110 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq1816 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1815 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1815
  have eq1839 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq112 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq1840 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1839 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1839
  have eq1841 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1840 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq1840 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq1840 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1840
  have eq3902 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq1841 x y
       grind)
    | exact superpose eq1841 eq75
    | (have j1 := eq1841 x y
       grind)
    | exact resolve eq75 eq1841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3960 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1841 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3967 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq3902
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3902
    | exact resolve eq3902 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3902
  have eq4004 : (k y x) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq3967
    | exact resolve eq3967 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3967
  have eq5871 : (k (σ y) (σ x)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq4004
       grind)
    | exact superpose eq4004 eq75
    | exact resolve eq75 eq4004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4004
  have eq5890 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq5871
       have i₂ := eq124
       grind)
    | exact superpose eq124 eq5871
    | exact resolve eq5871 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5871
  have eq10866 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq330 X0 X1 X1
       have i₂ := eq343 X1 X0 X0
       grind)
    | exact superpose eq343 eq330
    | (have j0 := eq330 X0 X1 x
       have j1 := eq343 X1 X1 X0
       grind)
    | exact resolve eq330 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330 eq343
  have eq10950 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq10866 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10866
  have eq11154 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5890
       have i₂ := eq1841 sF2 sF3
       grind)
    | exact superpose eq1841 eq5890
    | (have j1 := eq1841 (σ x) (σ y)
       grind)
    | exact resolve eq5890 eq1841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5890
  have eq11186 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11154
    | exact resolve eq11154 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11154
  have eq11196 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11186
    | exact resolve eq11186 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11186
  have eq11201 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq11196
       have r₂ := eq27
       grind)
    | exact resolve eq11196 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11196
  have eq11221 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11201 eq1816
    | (have j0 := eq1816 (σ x) (σ y)
       grind)
    | exact resolve eq1816 eq11201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11231 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11221
    | exact resolve eq11221 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11221
  have eq11252 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11231
    | exact resolve eq11231 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11231
  have eq11253 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq11252
  have eq11384 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq11253 eq52
    | exact resolve eq52 eq11253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11253
  have eq17310 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11384 eq53
    | exact resolve eq53 eq11384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq11384
  have eq17348 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq17310
    | exact resolve eq17310 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17310
  have eq17349 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17348
  have eq17354 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17349 eq122
    | exact resolve eq122 eq17349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17412 : ∀ X0 : G, (τ (σ x)) = (M.op (τ (M.op (σ x) (σ y))) (M.op (τ (σ x)) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq17349 eq1389
    | exact resolve eq1389 eq17349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1389
  have eq17419 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq17349 eq52
    | exact resolve eq52 eq17349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq17349
  have eq17445 : ∀ X0 : G, x = (M.op (τ (M.op (σ x) (σ y))) (M.op x X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq28 eq17412
    | exact resolve eq17412 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17412
  have eq17987 : x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17445 x
       have i₂ := eq17354
       grind)
    | exact superpose eq17354 eq17445
    | exact resolve eq17445 eq17354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17445
  have eq18026 : x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17987
  have eq18032 : x = (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18026
       have i₂ := eq1002 sF4
       grind)
    | exact superpose eq1002 eq18026
    | exact resolve eq18026 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002 eq18026
  have eq18068 : (k y x) = (τ (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18032 eq1039
    | exact resolve eq1039 eq18032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039 eq18032
  have eq20838 : (σ (k y x)) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18068 eq15
    | exact resolve eq15 eq18068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18068
  have eq20870 : (k (σ y) (σ x)) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20838
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq20838
    | exact resolve eq20838 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20838
  have eq20925 : (k (σ y) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20870 eq1841
    | exact resolve eq1841 eq20870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1841 eq20870
  have eq20930 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq388 eq20925
    | exact resolve eq20925 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388 eq20925
  have eq20954 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq51 eq20930
    | exact resolve eq20930 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq20930
  have eq20955 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20954
  have eq109502 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq3960
    | (have j0 := eq3960 (σ y) (σ x)
       grind)
    | exact resolve eq3960 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3960
  have eq109637 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq109502
       have r₂ := eq11201
       grind)
    | exact resolve eq109502 eq11201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11201 eq109502
  have eq109807 : (k y x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq109637 eq98
    | exact resolve eq98 eq109637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq109881 : (k y x) = (M.op x x) := by
    first
    | exact superpose eq122 eq109807
    | exact resolve eq109807 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109807
  have eq109939 : (M.op x x) = (M.op y y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1816 x y
       have i₂ := eq109881
       grind)
    | exact superpose eq109881 eq1816
    | (have j0 := eq1816 x y
       grind)
    | exact resolve eq1816 eq109881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1816
  have eq109942 : x = (M.op x y) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq109939
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq109939
    | exact resolve eq109939 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109939
  have eq109960 : (M.op x x) = (M.op y y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq109942
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq109942
    | exact resolve eq109942 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109942
  have eq118701 : (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq123
       have i₂ := eq109960
       grind)
    | exact superpose eq109960 eq123
    | exact resolve eq123 eq109960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq109960
  have eq118915 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq118701
       have i₂ := eq124
       grind)
    | exact superpose eq124 eq118701
    | exact resolve eq118701 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq118701
  have eq119151 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq118915 eq341
    | exact resolve eq341 eq118915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341 eq118915
  have eq119537 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17419 eq119151
    | exact resolve eq119151 eq17419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17419 eq119151
  have eq119656 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17354
       have i₂ := eq119537
       grind)
    | exact superpose eq119537 eq17354
    | exact resolve eq17354 eq119537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17354 eq119537
  have eq119924 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq119656
  have eq120014 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq119924 eq15
    | exact resolve eq15 eq119924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119924
  have eq120128 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq120014
    | exact resolve eq120014 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120014
  have eq120138 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq120128
       have r₂ := eq27
       grind)
    | exact resolve eq120128 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120128
  have eq120233 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq120138 eq27
    | exact resolve eq27 eq120138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120236 : (σ x) = (M.op (M.op (M.op x y) (σ x)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq120138 eq260
    | exact resolve eq260 eq120138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq120389 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq120236 eq355
    | exact resolve eq355 eq120236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355 eq120236
  have eq120558 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq120138 eq120389
    | exact resolve eq120389 eq120138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120138 eq120389
  have eq120655 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq120558
  have eq125303 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq75
       have i₂ := eq10950 y x
       grind)
    | exact superpose eq10950 eq75
    | (have j1 := eq10950 y x
       grind)
    | exact resolve eq75 eq10950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq10950
  have eq126268 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq109637 eq125303
    | exact resolve eq125303 eq109637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109637 eq125303
  have eq126618 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq126268
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq126268
    | exact resolve eq126268 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126268
  have eq126850 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq126618
    | exact resolve eq126618 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126618
  have eq127009 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq126850
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq126850
    | exact resolve eq126850 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126850
  have eq127161 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq127009 eq120655
    | exact resolve eq120655 eq127009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120655 eq127009
  have eq127377 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq127161
  have eq127389 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq127377
       have r₂ := eq120233
       grind)
    | exact resolve eq127377 eq120233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120233 eq127377
  have eq127469 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq127389 eq29
    | exact resolve eq29 eq127389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq127389
  have eq127705 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq127469
    | exact resolve eq127469 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq127469
  have eq127706 : x = (M.op x y) ∨ x = y := by grind
  clear eq127705
  have eq127727 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq127706 eq20
    | exact resolve eq20 eq127706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127926 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq127727
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq127727
    | exact resolve eq127727 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127727
  have eq128116 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq127926 eq20955
    | exact resolve eq20955 eq127926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20955
  have eq128603 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq128116
       have r₂ := eq27
       grind)
    | exact resolve eq128116 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128116
  have eq128870 : (k y (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq128603 eq108
    | exact resolve eq108 eq128603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq128603
  have eq129093 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq127706 eq128870
    | exact resolve eq128870 eq127706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128870
  have eq129121 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ x = y := by grind
  clear eq129093
  have eq129131 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq129121
       have i₂ := eq109881
       grind)
    | exact superpose eq109881 eq129121
    | exact resolve eq129121 eq109881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109881 eq129121
  have eq129455 : x = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq353 x
       have i₂ := eq129131
       grind)
    | exact superpose eq129131 eq353
    | exact resolve eq353 eq129131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131294 : x = (M.op (τ (M.op (σ x) (σ y))) x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq127706 eq129455
    | exact resolve eq129455 eq127706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129455
  have eq131374 : x = (M.op (τ (M.op (σ x) (σ y))) x) ∨ x = y := by grind
  clear eq131294
  have eq131400 : x = (M.op x (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq131374 eq353
    | exact resolve eq353 eq131374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353 eq131374
  have eq131482 : x = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq127706 eq131400
    | exact resolve eq131400 eq127706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127706 eq131400
  have eq131565 : x = (M.op x x) ∨ x = y := by grind
  clear eq131482
  have eq131632 : x = (τ (M.op (σ x) (σ y))) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq129131
       have i₂ := eq131565
       grind)
    | exact superpose eq131565 eq129131
    | exact resolve eq129131 eq131565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129131 eq131565
  have eq131833 : x = (τ (M.op (σ x) (σ y))) ∨ x = y := by grind
  clear eq131632
  have eq131928 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq131833 eq15
    | exact resolve eq15 eq131833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131833
  have eq132010 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq131928
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq131928
    | exact resolve eq131928 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131928
  have eq132020 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq132010 eq27
    | exact resolve eq27 eq132010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132010
  have eq132085 : x = y := by
    first
    | (have r₁ := eq132020
       have r₂ := eq127926
       grind)
    | exact resolve eq132020 eq127926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127926 eq132020
  have eq132086 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq132085
       grind)
    | exact superpose eq132085 eq18
    | exact resolve eq18 eq132085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq132087 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq132085
       grind)
    | exact superpose eq132085 eq24
    | exact resolve eq24 eq132085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq132085
  have eq132297 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq132087
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq132087
    | exact resolve eq132087 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq132087
  have eq132324 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq132297 eq26
    | exact resolve eq26 eq132297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq132297
  have eq132977 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq132324 eq122
    | exact resolve eq122 eq132324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq132324
  have eq133317 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq132977
       have i₂ := eq132086
       grind)
    | exact superpose eq132086 eq132977
    | exact resolve eq132977 eq132086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132086 eq132977
  have eq133383 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq133317 eq15
    | exact resolve eq15 eq133317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133317
  have eq133471 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq133383
    | exact resolve eq133383 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq133383
  have eq133508 : False := by grind
  exact eq133508

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pxy_pyx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
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
  have eq50 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq14 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 X1) x) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 X1 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) ≠ X0 ∨ (k (M.op X0 X3) (M.op (M.op X1 X2) X0)) = (M.op (M.op X0 X3) (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X0 X3) (M.op (M.op X1 X2) X0)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X0 X3) (M.op (M.op X1 X2) X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq77 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq78 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq93 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq78 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq78
    | (have j0 := eq78 (σ X0) (σ X1)
       grind)
    | exact resolve eq78 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq78 x y
       grind)
    | exact superpose eq78 eq44
    | (have j1 := eq78 x y
       grind)
    | exact resolve eq44 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (k (σ y) (σ (M.op x y))) = (σ (M.op y (M.op x y))) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq77
       have i₂ := eq78 y sF0
       grind)
    | exact superpose eq78 eq77
    | (have j1 := eq78 y (M.op x y)
       grind)
    | exact resolve eq77 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102
    | exact resolve eq102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq110
    | exact resolve eq110 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq130 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq141 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq130 eq16
    | exact resolve eq16 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq78 (σ X0) sF3
       grind)
    | exact superpose eq78 eq40
    | (have j1 := eq78 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq207 : x = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    first
    | (have i₁ := eq50 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) X0) := by
    intro X0
    first
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq52 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x y X0
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ x) (σ y) X0
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 X0 x y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 (σ x) (σ y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq313 : ∀ X2 : G, (M.op x y) = (M.op x (M.op (M.op x y) X2)) := by
    intro X2
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq358 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq388 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq38 X1 X0
       have i₂ := eq78 X0 (τ X1)
       grind)
    | exact superpose eq78 eq38
    | (have j1 := eq78 X0 (τ X1)
       grind)
    | exact resolve eq38 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq637 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq94 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq94 X0 X0
       grind)
    | exact resolve eq13 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq642 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X2 (σ X0)) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X2 (σ X0) (σ X1)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq52
    | (have j1 := eq94 X0 X1
       grind)
    | exact resolve eq52 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq649 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq637 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq637
    | (have j0 := eq637 X0 X1
       grind)
    | exact resolve eq637 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq738 : ∀ X0 : G, (k (τ X0) (k y (M.op x y))) = (τ (k X0 (k (σ y) (σ (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq77 eq358
    | exact resolve eq358 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq358 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq358
    | (have j0 := eq358 X0 x
       grind)
    | exact resolve eq358 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq935 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq112 eq78
    | (have j0 := eq78 (σ x) (σ y)
       grind)
    | exact resolve eq78 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq936 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq935
    | exact resolve eq935 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq939 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq936
       have r₂ := eq27
       grind)
    | exact resolve eq936 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq941 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq939 eq249
    | exact resolve eq249 eq939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq942 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq939 eq258
    | exact resolve eq258 eq939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq950 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq939 eq52
    | exact resolve eq52 eq939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939
  have eq1126 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq942 eq950
    | exact resolve eq950 eq942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942 eq950
  have eq1143 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq1126
  have eq1174 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1143 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq1143
       grind)
    | exact resolve eq13 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq1188 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq1174
  have eq1191 : (τ (σ x)) = (k x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1188 eq49
    | exact resolve eq49 eq1188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq1195 : x = (k x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28 eq1191
    | exact resolve eq1191 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191
  have eq1198 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq78 x x
       have i₂ := eq1195
       grind)
    | exact superpose eq1195 eq78
    | (have j0 := eq78 x x
       grind)
    | exact resolve eq78 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195
  have eq1199 : x = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq1198
  have eq1203 : x = (M.op x (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq257 y
       have i₂ := eq1199
       grind)
    | exact superpose eq1199 eq257
    | exact resolve eq257 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1211 : ∀ X0 : G, x = (M.op x (M.op x X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq52 y x X0
       have i₂ := eq1199
       grind)
    | exact superpose eq1199 eq52
    | exact resolve eq52 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199
  have eq1535 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1203 eq1211
    | exact resolve eq1211 eq1203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203 eq1211
  have eq1553 : x = (M.op x x) := by grind
  clear eq1535
  have eq1555 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq257 x
       have i₂ := eq1553
       grind)
    | exact superpose eq1553 eq257
    | exact resolve eq257 eq1553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1556 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq1553
       grind)
    | exact superpose eq1553 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq1553
       grind)
    | exact resolve eq13 eq1553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1559 : x = (M.op (M.op (M.op x y) x) x) := by
    first
    | (have i₁ := eq50 x x
       have i₂ := eq1553
       grind)
    | exact superpose eq1553 eq50
    | exact resolve eq50 eq1553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1561 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | (have i₁ := eq52 X0 x x
       have i₂ := eq1553
       grind)
    | exact superpose eq1553 eq52
    | exact resolve eq52 eq1553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1553
  have eq1571 : x = (k x x) := by grind
  clear eq1556
  have eq1574 : x ≠ x ∨ (M.op (M.op x y) x) = (k (M.op x y) x) := by
    first
    | exact superpose eq1555 eq13
    | (have j0 := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq1555
       grind)
    | exact resolve eq13 eq1555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1555
  have eq1589 : (M.op (M.op x y) x) = (k (M.op x y) x) := by grind
  clear eq1574
  have eq1592 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq1571
       grind)
    | exact superpose eq1571 eq43
    | exact resolve eq43 eq1571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1596 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1592
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1592
    | exact resolve eq1592 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1592
  have eq1599 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1596 eq78
    | (have j0 := eq78 (σ x) (σ x)
       grind)
    | exact resolve eq78 eq1596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1600 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1599
  have eq1606 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1600 eq258
    | exact resolve eq258 eq1600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq1613 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq1600 eq52
    | exact resolve eq52 eq1600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1600
  have eq1626 : (σ x) ≠ (σ x) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1606 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq1606
       grind)
    | exact resolve eq13 eq1606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1606
  have eq1641 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  clear eq1626
  have eq1644 : ∀ X0 : G, x ≠ x ∨ (k (M.op x X0) x) = (M.op (M.op x X0) x) := by
    intro X0
    first
    | exact superpose eq1559 eq68
    | (have r₁ := eq68 x (M.op x y) x x
       have r₂ := eq1559
       grind)
    | exact resolve eq68 eq1559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1559
  have eq1664 : ∀ X0 : G, (k (M.op x X0) x) = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq1644 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1644
  have eq1754 : (k (σ (M.op x y)) (σ x)) = (σ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq1589 eq130
    | exact resolve eq130 eq1589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq3901 : (σ (k (k x x) y)) = (M.op (k (σ x) (σ x)) (σ y)) ∨ (k (σ x) (σ x)) = (M.op (σ y) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq188 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq188
    | exact resolve eq188 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq188
  have eq3942 : (M.op (σ x) (σ y)) = (σ (k (k x x) y)) ∨ (k (σ x) (σ x)) = (M.op (σ y) (k (σ x) (σ x))) := by
    first
    | exact superpose eq1596 eq3901
    | exact resolve eq3901 eq1596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3901
  have eq3948 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (k (σ x) (σ x)) = (M.op (σ y) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq3942
       have i₂ := eq1571
       grind)
    | exact superpose eq1571 eq3942
    | exact resolve eq3942 eq1571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3942
  have eq3950 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (M.op (σ y) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq3948
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq3948
    | exact resolve eq3948 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3948
  have eq3951 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (M.op (σ y) (k (σ x) (σ x))) := by
    first
    | exact superpose eq26 eq3950
    | exact resolve eq3950 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3950
  have eq3952 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1596 eq3951
    | exact resolve eq3951 eq1596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3951
  have eq4046 : ∀ X0 : G, (k (σ X0) (k (σ x) (σ x))) = (σ (M.op X0 (k x x))) ∨ (M.op (k x x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq49 eq388
    | exact resolve eq388 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq4094 : ∀ X0 : G, (k (σ X0) (k (σ x) (σ x))) = (σ (M.op X0 x)) ∨ (M.op (k x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4046 X0
       have i₂ := eq1571
       grind)
    | exact superpose eq1571 eq4046
    | (have j0 := eq4046 X0
       grind)
    | exact resolve eq4046 eq1571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4046
  have eq4099 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op X0 x)) ∨ (M.op (k x x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1596 eq4094
    | (have j0 := eq4094 X0
       grind)
    | exact resolve eq4094 eq1596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4094
  have eq4101 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 x)) ∨ (M.op (k x x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq39 eq4099
    | (have j0 := eq4099 X0
       grind)
    | exact resolve eq4099 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq4099
  have eq4102 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 x)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4101 X0
       have i₂ := eq1571
       grind)
    | exact superpose eq1571 eq4101
    | (have j0 := eq4101 X0
       grind)
    | exact resolve eq4101 eq1571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4101
  have eq5018 : ∀ X0 : G, (σ (τ (k X0 (σ x)))) = (σ (M.op (τ X0) x)) ∨ (τ X0) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq4102 (τ X0)
       have i₂ := eq742 X0
       grind)
    | exact superpose eq742 eq4102
    | (have j0 := eq4102 (τ X0)
       grind)
    | exact resolve eq4102 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4102
  have eq5090 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (τ X0) x)) ∨ (τ X0) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq5018 X0
       have i₂ := eq15 (k X0 sF2)
       grind)
    | exact superpose eq15 eq5018
    | (have j0 := eq5018 X0
       grind)
    | exact resolve eq5018 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5018
  have eq5889 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ (M.op (M.op x y) x))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1589 eq642
    | (have j0 := eq642 (M.op x y) x x
       grind)
    | exact resolve eq642 eq1589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq6000 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (k (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1754 eq5889
    | exact resolve eq5889 eq1754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5889
  have eq6050 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (k (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq6000
    | (have j0 := eq6000 X0
       grind)
    | exact resolve eq6000 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6000
  have eq6086 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (k (σ (M.op x y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq20 eq6050
    | (have j0 := eq6050 X0
       grind)
    | exact resolve eq6050 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6050
  have eq6099 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (k (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq6086 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6086
    | (have j0 := eq6086 X0
       grind)
    | exact resolve eq6086 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6086
  have eq7798 : (σ y) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq649 y x
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq649
    | (have j0 := eq649 y x
       grind)
    | exact resolve eq649 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq7838 : (σ y) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7798
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7798
    | exact resolve eq7798 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7798
  have eq7908 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7838
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq7838
    | exact resolve eq7838 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7838
  have eq7963 : (k (σ x) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7908
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7908
    | exact resolve eq7908 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7908
  have eq8010 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7963
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7963
    | exact resolve eq7963 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7963
  have eq8055 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq8010
    | exact resolve eq8010 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8010
  have eq8096 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq8055
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8055
    | exact resolve eq8055 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8055
  have eq8125 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq8096
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8096
    | exact resolve eq8096 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8096
  have eq8137 : (σ y) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq8125
    | exact resolve eq8125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8125
  have eq15503 : ∀ X0 : G, (τ (k X0 (σ x))) = (M.op (τ X0) x) ∨ (τ X0) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) x)
       have i₂ := eq5090 X0
       grind)
    | exact superpose eq5090 eq16
    | (have j1 := eq5090 X0
       grind)
    | exact resolve eq16 eq5090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5090
  have eq16559 : ∀ X0 : G, x = (M.op (τ (k X0 (σ x))) x) ∨ (τ X0) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1561 (τ X0)
       have i₂ := eq15503 X0
       grind)
    | exact superpose eq15503 eq1561
    | (have j1 := eq15503 X0
       grind)
    | exact resolve eq1561 eq15503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15503
  have eq17672 : x = (M.op (τ (M.op (M.op (σ x) (σ y)) (σ x))) x) ∨ (τ (M.op (σ x) (σ y))) = (M.op x (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1641 eq16559
    | (have j0 := eq16559 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq16559 eq1641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16559
  have eq18376 : x = (M.op (τ (σ y)) x) ∨ (τ (M.op (σ x) (σ y))) = (M.op x (τ (M.op (σ x) (σ y)))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq941 eq17672
    | exact resolve eq17672 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17672
  have eq18419 : x = (M.op y x) ∨ (τ (M.op (σ x) (σ y))) = (M.op x (τ (M.op (σ x) (σ y)))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq18376
    | exact resolve eq18376 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18376
  have eq18420 : (τ (M.op (σ x) (σ y))) = (M.op x (τ (M.op (σ x) (σ y)))) ∨ x = (M.op y x) := by grind
  clear eq18419
  have eq18510 : (M.op (τ (M.op (σ x) (σ y))) x) = (k (τ (M.op (σ x) (σ y))) x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq18420 eq1664
    | exact resolve eq1664 eq18420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1664 eq18420
  have eq18548 : (τ (k (M.op (σ x) (σ y)) (σ x))) = (M.op (τ (M.op (σ x) (σ y))) x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq18510
       have i₂ := eq742 sF4
       grind)
    | exact superpose eq742 eq18510
    | exact resolve eq18510 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq18510
  have eq18553 : (τ (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op (τ (M.op (σ x) (σ y))) x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1641 eq18548
    | exact resolve eq18548 eq1641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1641 eq18548
  have eq22844 : x = (M.op (τ (M.op (M.op (σ x) (σ y)) (σ x))) (M.op x y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq18553 eq257
    | exact resolve eq257 eq18553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257 eq18553
  have eq22883 : x = (M.op (τ (σ y)) (M.op x y)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq941 eq22844
    | exact resolve eq22844 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941 eq22844
  have eq22912 : x = (M.op (τ (σ y)) (M.op x y)) ∨ x = (M.op y x) := by grind
  clear eq22883
  have eq22917 : x = (M.op y (M.op x y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq22912
    | exact resolve eq22912 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22912
  have eq22920 : y = (M.op (M.op x y) x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq22917 eq248
    | exact resolve eq248 eq22917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22917
  have eq22987 : x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq22920 eq1561
    | exact resolve eq1561 eq22920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1561 eq22920
  have eq23020 : x = (M.op y x) := by grind
  clear eq22987
  have eq23061 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq248 x
       have i₂ := eq23020
       grind)
    | exact superpose eq23020 eq248
    | exact resolve eq248 eq23020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq23067 : x ≠ y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq23020
       grind)
    | exact superpose eq23020 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq23020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23070 : y = (M.op (M.op (M.op x y) y) x) := by
    first
    | (have i₁ := eq50 y x
       have i₂ := eq23020
       grind)
    | exact superpose eq23020 eq50
    | exact resolve eq50 eq23020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq23020
  have eq23095 : x ≠ y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq23067
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23067
    | exact resolve eq23067 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq23067
  have eq23205 : x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq23061 eq207
    | exact resolve eq207 eq23061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq23209 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq23061 eq1754
    | exact resolve eq1754 eq23061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1754
  have eq23285 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq23209
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23209
    | exact resolve eq23209 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23209
  have eq23486 : y ≠ (M.op (M.op x y) y) ∨ (k x (M.op (M.op x y) y)) = (M.op x (M.op (M.op x y) y)) := by
    first
    | exact superpose eq23070 eq13
    | (have j0 := eq13 x (M.op (M.op x y) y)
       grind)
    | exact resolve eq13 eq23070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23070
  have eq23511 : y ≠ (M.op (M.op x y) y) ∨ (M.op x y) = (k x (M.op (M.op x y) y)) := by
    first
    | exact superpose eq313 eq23486
    | exact resolve eq23486 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313 eq23486
  have eq27352 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq23205 eq105
    | exact resolve eq105 eq23205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq23205
  have eq27353 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq27352
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27352
    | exact resolve eq27352 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27352
  have eq27357 : (τ (σ x)) = (k y (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq27353 eq93
    | exact resolve eq93 eq27353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq27353
  have eq27367 : y = (M.op (M.op x y) y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq28 eq27357
    | exact resolve eq27357 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27357
  have eq27379 : y = (M.op (M.op (M.op x y) y) y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq27367 eq210
    | exact resolve eq210 eq27367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq28741 : y = (M.op y y) ∨ x = (k y (M.op x y)) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq27367 eq27379
    | exact resolve eq27379 eq27367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27379
  have eq28781 : y = (M.op y y) ∨ x = (k y (M.op x y)) := by grind
  clear eq28741
  have eq28798 : y ≠ y ∨ y = (k y y) ∨ x = (k y (M.op x y)) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq28781
       grind)
    | exact superpose eq28781 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq28781
       grind)
    | exact resolve eq13 eq28781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28781
  have eq28828 : y = (k y y) ∨ x = (k y (M.op x y)) := by grind
  clear eq28798
  have eq28851 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (k y (M.op x y)) := by
    first
    | (have i₁ := eq649 y y
       have i₂ := eq28828
       grind)
    | exact superpose eq28828 eq649
    | (have j0 := eq649 y y
       grind)
    | exact resolve eq649 eq28828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649 eq28828
  have eq28854 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (k y (M.op x y)) := by grind
  clear eq28851
  have eq28855 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (k y (M.op x y)) := by grind
  clear eq28854
  have eq28861 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (k y (M.op x y)) := by
    first
    | (have i₁ := eq28855
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq28855
    | exact resolve eq28855 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28855
  have eq28891 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ x = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq28861 eq52
    | exact resolve eq52 eq28861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq28861
  have eq30456 : (k (k x x) (k y (M.op x y))) = (τ (k (k (σ x) (σ x)) (k (σ y) (σ (M.op x y))))) := by
    first
    | exact superpose eq49 eq738
    | exact resolve eq738 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq738
  have eq30510 : (τ (k (σ x) (k (σ y) (σ (M.op x y))))) = (k (k x x) (k y (M.op x y))) := by
    first
    | exact superpose eq1596 eq30456
    | exact resolve eq30456 eq1596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596 eq30456
  have eq30541 : (k x (k y (M.op x y))) = (τ (k (σ x) (k (σ y) (σ (M.op x y))))) := by
    first
    | (have i₁ := eq30510
       have i₂ := eq1571
       grind)
    | exact superpose eq1571 eq30510
    | exact resolve eq30510 eq1571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30510
  have eq34653 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq27367 eq23511
    | (have r₁ := eq23511
       have r₂ := eq27367
       grind)
    | exact resolve eq23511 eq27367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23511 eq27367
  have eq34654 : (M.op x y) = (k x y) ∨ x = (k y (M.op x y)) := by grind
  clear eq34653
  have eq34662 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y (M.op x y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq34654
       grind)
    | exact superpose eq34654 eq44
    | exact resolve eq44 eq34654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq34654
  have eq34722 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq20 eq34662
    | exact resolve eq34662 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34662
  have eq34774 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq34722 eq3952
    | exact resolve eq3952 eq34722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3952
  have eq34817 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k y (M.op x y)) := by
    first
    | (have r₁ := eq34774
       have r₂ := eq27
       grind)
    | exact resolve eq34774 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34774
  have eq34828 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (k y (M.op x y)) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq34817 eq28891
    | exact resolve eq28891 eq34817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28891 eq34817
  have eq34864 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (k y (M.op x y)) := by grind
  clear eq34828
  have eq34940 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq34864 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq34864
       grind)
    | exact resolve eq13 eq34864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34864
  have eq34968 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k y (M.op x y)) := by grind
  clear eq34940
  have eq34972 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq26 eq34968
    | exact resolve eq34968 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34968
  have eq35139 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y (M.op x y)) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq34972 eq34722
    | exact resolve eq34722 eq34972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34722 eq34972
  have eq35153 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y (M.op x y)) := by grind
  clear eq35139
  have eq35156 : x = (k y (M.op x y)) := by
    first
    | (have r₁ := eq35153
       have r₂ := eq27
       grind)
    | exact resolve eq35153 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35153
  have eq35160 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq35156 eq77
    | exact resolve eq77 eq35156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq35198 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq35160
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35160
    | exact resolve eq35160 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35160
  have eq35580 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq35198
       have i₂ := eq78 sF3 sF1
       grind)
    | exact superpose eq78 eq35198
    | (have j1 := eq78 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq35198 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq37028 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq35580 eq12
    | (have r₁ := eq12 (σ y) (σ (M.op x y))
       have r₂ := eq35580
       grind)
    | exact resolve eq12 eq35580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37029 : (σ (M.op x y)) ≠ (σ y) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq35580 eq13
    | (have j0 := eq13 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq13 eq35580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35580
  have eq37055 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by grind
  clear eq37028
  have eq37056 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq35198 eq37029
    | exact resolve eq37029 eq35198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37029
  have eq37057 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by grind
  clear eq37056
  have eq37058 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq35198 eq37055
    | exact resolve eq37055 eq35198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37055
  have eq37766 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq37058
       have r₂ := eq37057
       grind)
    | exact resolve eq37058 eq37057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37057 eq37058
  have eq38123 : (σ (M.op x y)) = (M.op (σ x) (k (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq37766 eq6099
    | exact resolve eq6099 eq37766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6099 eq37766
  have eq38151 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq23285 eq38123
    | exact resolve eq38123 eq23285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38123
  have eq38152 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq38151
    | exact resolve eq38151 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq38151
  have eq38153 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq38152
       have r₂ := eq27
       grind)
    | exact resolve eq38152 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38152
  have eq38210 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq38153 eq1613
    | exact resolve eq1613 eq38153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1613
  have eq39443 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq38210 eq38153
    | exact resolve eq38153 eq38210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38153 eq38210
  have eq39482 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq39443
  have eq39491 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq39482 eq29
    | exact resolve eq29 eq39482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq39482
  have eq39724 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq28 eq39491
    | exact resolve eq39491 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq39491
  have eq40360 : (k x (k y (M.op x y))) = (τ (k (σ (M.op x y)) (k (σ y) (σ (M.op x y))))) ∨ x = y := by
    first
    | exact superpose eq39724 eq30541
    | exact resolve eq30541 eq39724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30541 eq39724
  have eq40416 : (k x (k y (M.op x y))) = (τ (k (σ (M.op x y)) (σ x))) ∨ x = y := by
    first
    | exact superpose eq35198 eq40360
    | exact resolve eq40360 eq35198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40360
  have eq40510 : (k x (k y (M.op x y))) = (k (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq141 eq40416
    | exact resolve eq40416 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq40416
  have eq40541 : (k x (k y (M.op x y))) = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq1589 eq40510
    | exact resolve eq40510 eq1589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1589 eq40510
  have eq40548 : y = (k x (k y (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq23061 eq40541
    | exact resolve eq40541 eq23061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23061 eq40541
  have eq40552 : y = (k x x) ∨ x = y := by
    first
    | exact superpose eq35156 eq40548
    | exact resolve eq40548 eq35156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35156 eq40548
  have eq40554 : x = y ∨ x = y := by
    first
    | (have i₁ := eq40552
       have i₂ := eq1571
       grind)
    | exact superpose eq1571 eq40552
    | exact resolve eq40552 eq1571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40552
  have eq40555 : x = y := by grind
  clear eq40554
  have eq40559 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq40555
       grind)
    | exact superpose eq40555 eq24
    | exact resolve eq24 eq40555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq40707 : x ≠ x ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq23095
       have i₂ := eq40555
       grind)
    | exact superpose eq40555 eq23095
    | (have r₁ := eq23095
       have r₂ := eq40555
       grind)
    | exact resolve eq23095 eq40555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23095 eq40555
  have eq40732 : (M.op x y) = (k x x) := by grind
  clear eq40707
  have eq40746 : x = (M.op x y) := by
    first
    | (have i₁ := eq40732
       have i₂ := eq1571
       grind)
    | exact superpose eq1571 eq40732
    | exact resolve eq40732 eq1571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1571 eq40732
  have eq40846 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq40559
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq40559
    | exact resolve eq40559 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40559
  have eq40952 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq40746 eq20
    | exact resolve eq20 eq40746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq40746
  have eq41225 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq40952
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq40952
    | exact resolve eq40952 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq40952
  have eq41777 : (σ y) ≠ (k (σ y) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41225 eq8137
    | exact resolve eq8137 eq41225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8137
  have eq41989 : (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35198 eq41777
    | exact resolve eq41777 eq35198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35198 eq41777
  have eq42107 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq41989
       have r₂ := eq40846
       grind)
    | exact resolve eq41989 eq40846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41989
  have eq42188 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40846 eq42107
    | exact resolve eq42107 eq40846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42107
  have eq42244 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23285 eq42188
    | exact resolve eq42188 eq23285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23285 eq42188
  have eq42245 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq42244
  have eq42287 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40846 eq42245
    | exact resolve eq42245 eq40846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40846 eq42245
  have eq42319 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41225 eq42287
    | exact resolve eq42287 eq41225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41225 eq42287
  have eq42335 : False := by grind
  exact eq42335
