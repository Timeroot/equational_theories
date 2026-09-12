import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_pyy_pxy_Equation422 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law422 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X2 X0))) = (M.op (M.op X0 (M.op X1 (M.op X2 X0))) (M.op (M.op X0 (M.op X1 (M.op X2 X0))) (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 (M.op X1 (M.op X2 X0))) X3 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X2 X0)) X0 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq85 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq25
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq25 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq89 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq134 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op X3 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 (M.op X0 (M.op X1 (M.op X2 X0))) X1 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq21
    | exact resolve eq21 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq204 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq86 x y
       grind)
    | exact superpose eq86 eq16
    | (have j1 := eq86 x y
       grind)
    | exact resolve eq16 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq86 X0 X1
       grind)
    | exact superpose eq86 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq86 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq86 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq86 X0 X0
       grind)
    | exact resolve eq13 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq206 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq215 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq213 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq213 X0 X0
       have r₂ := eq13 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq213 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq213 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq218 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq215 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq215
    | (have j0 := eq215 X0 X1
       grind)
    | exact resolve eq215 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq243 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X0))) (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X0)))))) = (M.op (M.op (M.op X0 (M.op X1 (M.op X2 X0))) (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X0)))))) (M.op (M.op (M.op X0 (M.op X1 (M.op X2 X0))) (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X0)))))) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20 (M.op X0 (M.op X1 (M.op X2 X0))) X3 X4 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq445 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 (M.op (M.op X0 (M.op X1 (M.op X2 X0))) (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X0)))))))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq134 (M.op X0 (M.op X1 (M.op X2 X0))) X0 X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq134
    | exact resolve eq134 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq89 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq89
    | exact resolve eq89 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq508 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq469 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq469
    | (have j0 := eq469 X0 X1
       grind)
    | exact resolve eq469 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq1107 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq204
       have i₂ := eq508 x y
       grind)
    | exact superpose eq508 eq204
    | (have j1 := eq508 (σ x) (σ y)
       grind)
    | (have r₁ := eq204
       have r₂ := eq508 x y
       grind)
    | exact resolve eq204 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq1108 : y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq1107
  have eq1327 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq218 (τ X1) (τ X0)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq218
    | (have j0 := eq218 (τ (k X0 X1)) (τ X1)
       grind)
    | exact resolve eq218 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq1348 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1327 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1327
    | (have j0 := eq1327 X0 X1
       grind)
    | exact resolve eq1327 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327
  have eq1356 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1348 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1348
    | (have j0 := eq1348 X0 X1
       grind)
    | exact resolve eq1348 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1348
  have eq1362 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1356 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1356
    | (have j0 := eq1356 X0 X1
       grind)
    | exact resolve eq1356 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1356
  have eq1367 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1362 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1362
    | (have j0 := eq1362 X0 X1
       grind)
    | exact resolve eq1362 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1362
  have eq1370 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1367 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1367
    | (have j0 := eq1367 X0 X1
       grind)
    | exact resolve eq1367 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367
  have eq1373 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1370 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1370
    | (have j0 := eq1370 X0 X1
       grind)
    | exact resolve eq1370 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370
  have eq4171 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X5 X0) = (M.op (M.op X5 X0) (M.op (M.op X5 X0) (M.op X0 (M.op (M.op X0 (M.op X1 (M.op X2 X0))) (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X0))))))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq134 X0 X5 (M.op (M.op X0 (M.op X1 (M.op X2 X0))) (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X0)))))) (M.op (M.op X0 (M.op X1 (M.op X2 X0))) (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X0))))))
       have i₂ := eq243 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq243 eq134
    | exact resolve eq134 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq7984 : ∀ X0 X1 X2 X3 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) (M.op X2 (M.op X3 (σ X0)))))) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (M.op (σ X0) (σ X0)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq134 (σ X1) X0 X2 X3
       have i₂ := eq85 X0 X1
       grind)
    | exact superpose eq85 eq134
    | (have j1 := eq85 X1 X0
       grind)
    | exact resolve eq134 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8021 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq85 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq8022 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq8021 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8021
  have eq8028 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq8022 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8022
    | (have j0 := eq8022 X0
       grind)
    | exact resolve eq8022 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8022
  have eq8036 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (M.op (σ X0) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7984 X0 X1 x x
       have i₂ := eq9 (σ X0) x x
       grind)
    | exact superpose eq9 eq7984
    | (have j0 := eq7984 X0 X1 x x
       grind)
    | exact resolve eq7984 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7984
  have eq8071 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq8028 X0
       grind)
    | exact superpose eq8028 eq39
    | (have j1 := eq8028 X0
       grind)
    | exact resolve eq39 eq8028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq8028
  have eq8110 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq8071 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8071
    | (have j0 := eq8071 X0
       grind)
    | exact resolve eq8071 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8071
  have eq8111 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq8110 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8110
  have eq8116 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8111 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8111
    | exact resolve eq8111 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8152 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq8111 X0
       grind)
    | exact superpose eq8111 eq11
    | exact resolve eq11 eq8111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8226 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8116 X0
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq8116
    | exact resolve eq8116 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq8116
  have eq8291 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq8226 X0
       grind)
    | exact superpose eq8226 eq11
    | exact resolve eq11 eq8226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8226
  have eq8406 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq8291 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq8291
    | exact resolve eq8291 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8291
  have eq8863 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq8877 : ∀ X0 X1 X2 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (M.op (σ (k X0 X0)) (M.op (σ X0) (M.op X1 (M.op X2 (σ X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq134 (σ X0) (σ X0) X2 x
       have i₂ := eq8152 X0
       grind)
    | exact superpose eq8152 eq134
    | exact resolve eq134 eq8152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq8929 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (M.op (σ (M.op X0 X0)) (M.op (σ X0) (M.op X1 (M.op X2 (σ X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8877 X0 X1 X2
       have i₂ := eq8406 X0
       grind)
    | exact superpose eq8406 eq8877
    | exact resolve eq8877 eq8406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8877
  have eq8941 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq8863 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq8863
    | exact resolve eq8863 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8863
  have eq8995 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq8941 X0
       have i₂ := eq8406 X0
       grind)
    | exact superpose eq8406 eq8941
    | exact resolve eq8941 eq8406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8941
  have eq9033 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq8995
  have eq160827 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X0) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (M.op (σ X0) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8111 X0
       have i₂ := eq8036 X0 X1
       grind)
    | exact superpose eq8036 eq8111
    | (have j1 := eq8036 X0 X1
       grind)
    | exact resolve eq8111 eq8036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8036 eq8111
  have eq161015 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (M.op (σ X0) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq160827 X0 X1
       have i₂ := eq8406 X0
       grind)
    | exact superpose eq8406 eq160827
    | (have j0 := eq160827 X0 X1
       grind)
    | exact resolve eq160827 eq8406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160827
  have eq161113 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (M.op (σ X0) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq161015 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq161015
    | (have j0 := eq161015 X0 X1
       grind)
    | exact resolve eq161015 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161015
  have eq161181 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (M.op X0 X0) = X0 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq161113 X0 X1
       have i₂ := eq8152 X0
       grind)
    | exact superpose eq8152 eq161113
    | (have j0 := eq161113 X0 X1
       grind)
    | exact resolve eq161113 eq8152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161113
  have eq161234 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (M.op X0 X0) = X0 ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq161181 X0 X1
       have i₂ := eq8406 X0
       grind)
    | exact superpose eq8406 eq161181
    | (have j0 := eq161181 X0 X1
       grind)
    | exact resolve eq161181 eq8406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161181
  have eq640903 : ∀ X0 X1 X2 X3 : G, y = (M.op y (M.op y (M.op y (M.op (M.op y (M.op X0 (M.op X1 y))) (M.op X2 (M.op X3 (M.op y (M.op X0 (M.op X1 y))))))))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4171 y X1 X2 X3 x x
       have i₂ := eq1108
       grind)
    | exact superpose eq1108 eq4171
    | exact resolve eq4171 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108 eq4171
  have eq640934 : y = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq640903 x x x x
       have i₂ := eq445 y x x x x
       grind)
    | exact superpose eq445 eq640903
    | exact resolve eq640903 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445 eq640903
  have eq641028 : (σ x) = (σ (k y y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq640934
       have i₂ := eq8152 y
       grind)
    | exact superpose eq8152 eq640934
    | exact resolve eq640934 eq8152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640934
  have eq641113 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq641028
       have i₂ := eq8406 y
       grind)
    | exact superpose eq8406 eq641028
    | exact resolve eq641028 eq8406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641028
  have eq642991 : (k (τ (σ x)) y) = (τ (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq161234 y (σ x)
       have i₂ := eq641113
       grind)
    | exact superpose eq641113 eq161234
    | (have j0 := eq161234 y (σ x)
       grind)
    | exact resolve eq161234 eq641113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161234 eq641113
  have eq643099 : (k (τ (σ x)) y) = (τ (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq642991
  have eq643129 : y = (k (τ (σ x)) y) ∨ y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq643099
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq643099
    | exact resolve eq643099 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643099
  have eq643180 : y = (k x y) ∨ y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq643129
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq643129
    | exact resolve eq643129 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643129
  have eq643302 : y ≠ y ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1373 x y
       have i₂ := eq643180
       grind)
    | exact superpose eq643180 eq1373
    | (have j0 := eq1373 y y
       grind)
    | (have r₁ := eq1373 x y
       have r₂ := eq643180
       grind)
    | exact resolve eq1373 eq643180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1373 eq643180
  have eq643398 : y ≠ y ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq643302
  have eq643399 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq643398
  have eq645637 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op X0 (M.op X1 (σ y)))))) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0 X1
    first
    | (have i₁ := eq8929 y X1 x
       have i₂ := eq643399
       grind)
    | exact superpose eq643399 eq8929
    | exact resolve eq8929 eq643399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8929 eq643399
  have eq645821 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq645637 x x
       have i₂ := eq9 (σ y) x x
       grind)
    | exact superpose eq9 eq645637
    | exact resolve eq645637 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645637
  have eq645836 : (σ y) = (σ (k y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq645821
       have i₂ := eq8152 y
       grind)
    | exact superpose eq8152 eq645821
    | exact resolve eq645821 eq8152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645821
  have eq645842 : x = (M.op y y) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq645836
       have i₂ := eq8406 y
       grind)
    | exact superpose eq8406 eq645836
    | exact resolve eq645836 eq8406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645836
  have eq647730 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9033 y
       have i₂ := eq645842
       grind)
    | exact superpose eq645842 eq9033
    | exact resolve eq9033 eq645842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645842
  have eq647973 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq647730
       have r₂ := eq16
       grind)
    | exact resolve eq647730 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647730
  have eq649341 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op y y))) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 (M.op y y)
       have i₂ := eq647973
       grind)
    | exact superpose eq647973 eq15
    | exact resolve eq15 eq647973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647973
  have eq650236 : ∀ X0 : G, (σ x) = (σ (M.op y y)) ∨ (σ (k X0 y)) = (σ (k X0 (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq649341 X0
       have i₂ := eq15 X0 y
       grind)
    | exact superpose eq15 eq649341
    | exact resolve eq649341 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649341
  have eq666573 : ∀ X0 : G, (M.op y y) = (τ (σ x)) ∨ (σ (k X0 y)) = (σ (k X0 (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq650236 X0
       grind)
    | exact superpose eq650236 eq10
    | (have j1 := eq650236 X0
       grind)
    | exact resolve eq10 eq650236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650236
  have eq667472 : ∀ X0 : G, x = (M.op y y) ∨ (σ (k X0 y)) = (σ (k X0 (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq666573 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq666573
    | (have j0 := eq666573 X0
       grind)
    | exact resolve eq666573 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666573
  have eq667981 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (k X0 y)) = (σ (k X0 (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq9033 y
       have i₂ := eq667472 X0
       grind)
    | exact superpose eq667472 eq9033
    | (have j1 := eq667472 X0
       grind)
    | exact resolve eq9033 eq667472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9033 eq667472
  have eq668232 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 (M.op y y))) := by
    intro X0
    first
    | (have j0 := eq667981 X0
       grind)
    | (have r₁ := eq667981 X0
       have r₂ := eq16
       grind)
    | exact resolve eq667981 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667981
  have eq670854 : (σ (k (M.op y y) y)) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq668232 (M.op y y)
       have i₂ := eq8406 (M.op y y)
       grind)
    | exact superpose eq8406 eq668232
    | exact resolve eq668232 eq8406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq670962 : ∀ X0 : G, (k X0 (M.op y y)) = (τ (σ (k X0 y))) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 (M.op y y))
       have i₂ := eq668232 X0
       grind)
    | exact superpose eq668232 eq10
    | exact resolve eq10 eq668232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668232
  have eq671862 : ∀ X0 : G, (k X0 y) = (k X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq670962 X0
       have i₂ := eq10 (k X0 y)
       grind)
    | exact superpose eq10 eq670962
    | exact resolve eq670962 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670962
  have eq671946 : (σ (M.op (M.op y y) y)) = (σ (M.op (M.op y y) (M.op y y))) := by grind
  clear eq670854
  have eq672888 : (k (M.op y y) y) = (M.op (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq8406 (M.op y y)
       have i₂ := eq671862 (M.op y y)
       grind)
    | exact superpose eq671862 eq8406
    | exact resolve eq8406 eq671862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671862
  have eq673411 : (M.op (M.op y y) y) = (M.op (M.op y y) (M.op y y)) := by grind
  clear eq672888
  have eq691276 : y = (M.op y (M.op y (M.op (M.op y y) y))) := by
    first
    | (have i₁ := eq9 y (M.op y y) y
       have i₂ := eq673411
       grind)
    | exact superpose eq673411 eq9
    | exact resolve eq9 eq673411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673411
  have eq691862 : y = (M.op y y) := by
    first
    | (have i₁ := eq9 y y (M.op y y)
       have i₂ := eq691276
       grind)
    | exact superpose eq691276 eq9
    | exact resolve eq9 eq691276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691276
  have eq717531 : ∀ X0 : G, (σ (k X0 (M.op (M.op y y) (M.op y y)))) = (M.op (σ X0) (σ (M.op (M.op y y) y))) ∨ (σ (M.op (M.op y y) y)) = (M.op (σ X0) (σ (M.op (M.op y y) y))) ∨ (σ X0) = (M.op (σ (M.op (M.op y y) y)) (σ (M.op (M.op y y) y))) := by
    intro X0
    first
    | (have i₁ := eq86 X0 (M.op (M.op y y) (M.op y y))
       have i₂ := eq671946
       grind)
    | exact superpose eq671946 eq86
    | (have j0 := eq86 X0 (M.op (M.op y y) y)
       grind)
    | exact resolve eq86 eq671946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq718462 : ∀ X0 : G, (σ (k X0 (M.op y y))) = (M.op (σ X0) (σ (M.op y y))) ∨ (σ (M.op (M.op y y) y)) = (M.op (σ X0) (σ (M.op (M.op y y) y))) ∨ (σ X0) = (M.op (σ (M.op (M.op y y) y)) (σ (M.op (M.op y y) y))) := by
    intro X0
    first
    | (have i₁ := eq717531 X0
       have i₂ := eq691862
       grind)
    | exact superpose eq691862 eq717531
    | (have j0 := eq717531 X0
       grind)
    | exact resolve eq717531 eq691862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717531
  have eq718829 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op (M.op y y) y)) = (M.op (σ X0) (σ (M.op (M.op y y) y))) ∨ (σ X0) = (M.op (σ (M.op (M.op y y) y)) (σ (M.op (M.op y y) y))) := by
    intro X0
    first
    | (have i₁ := eq718462 X0
       have i₂ := eq691862
       grind)
    | exact superpose eq691862 eq718462
    | (have j0 := eq718462 X0
       grind)
    | exact resolve eq718462 eq691862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718462
  have eq719075 : ∀ X0 : G, (σ (M.op y y)) = (M.op (σ X0) (σ (M.op y y))) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ (M.op (M.op y y) y)) (σ (M.op (M.op y y) y))) := by
    intro X0
    first
    | (have i₁ := eq718829 X0
       have i₂ := eq691862
       grind)
    | exact superpose eq691862 eq718829
    | (have j0 := eq718829 X0
       grind)
    | exact resolve eq718829 eq691862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718829
  have eq719304 : ∀ X0 : G, (σ y) = (M.op (σ X0) (σ y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ (M.op (M.op y y) y)) (σ (M.op (M.op y y) y))) := by
    intro X0
    first
    | (have i₁ := eq719075 X0
       have i₂ := eq691862
       grind)
    | exact superpose eq691862 eq719075
    | (have j0 := eq719075 X0
       grind)
    | exact resolve eq719075 eq691862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719075
  have eq719525 : ∀ X0 : G, (σ X0) = (σ (k (M.op (M.op y y) y) (M.op (M.op y y) y))) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq719304 X0
       have i₂ := eq8152 (M.op (M.op y y) y)
       grind)
    | exact superpose eq8152 eq719304
    | (have j0 := eq719304 X0
       grind)
    | exact resolve eq719304 eq8152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719304
  have eq719717 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op (M.op y y) y) (M.op (M.op y y) y))) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq719525 X0
       have i₂ := eq8406 (M.op (M.op y y) y)
       grind)
    | exact superpose eq8406 eq719525
    | (have j0 := eq719525 X0
       grind)
    | exact resolve eq719525 eq8406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719525
  have eq719898 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op y y) (M.op y y))) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq719717 X0
       have i₂ := eq691862
       grind)
    | exact superpose eq691862 eq719717
    | (have j0 := eq719717 X0
       grind)
    | exact resolve eq719717 eq691862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719717
  have eq719986 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op y y) y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq719898 X0
       have i₂ := eq671946
       grind)
    | exact superpose eq671946 eq719898
    | (have j0 := eq719898 X0
       grind)
    | exact resolve eq719898 eq671946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671946 eq719898
  have eq720065 : ∀ X0 : G, (σ X0) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq719986 X0
       have i₂ := eq691862
       grind)
    | exact superpose eq691862 eq719986
    | (have j0 := eq719986 X0
       grind)
    | exact resolve eq719986 eq691862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719986
  have eq720141 : ∀ X0 : G, (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq720065 X0
       have i₂ := eq691862
       grind)
    | exact superpose eq691862 eq720065
    | (have j0 := eq720065 X0
       grind)
    | exact resolve eq720065 eq691862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720065
  have eq1151055 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ X0) = (σ y) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 (σ X0) (σ y)
       have i₂ := eq720141 X0
       grind)
    | exact superpose eq720141 eq13
    | (have j0 := eq13 (σ X0) (σ y)
       have j1 := eq720141 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ y)
       have r₂ := eq720141 X0
       grind)
    | exact resolve eq13 eq720141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1151230 : ∀ X0 : G, (σ y) ≠ (σ (k X0 y)) ∨ (σ X0) = (σ y) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq720141 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720141
  have eq1151231 : ∀ X0 : G, (M.op (σ y) (σ y)) = (k (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ X0) = (σ y) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1151055 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151055
  have eq1151269 : ∀ X0 : G, (M.op (σ y) (σ y)) = (σ (k X0 y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ X0) = (σ y) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1151231 X0
       have i₂ := eq15 X0 y
       grind)
    | exact superpose eq15 eq1151231
    | (have j0 := eq1151231 X0
       grind)
    | exact resolve eq1151231 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151231
  have eq1151385 : ∀ X0 : G, (σ (k y y)) = (σ (k X0 y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ X0) = (σ y) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1151269 X0
       have i₂ := eq8152 y
       grind)
    | exact superpose eq8152 eq1151269
    | (have j0 := eq1151269 X0
       grind)
    | exact resolve eq1151269 eq8152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151269
  have eq1151483 : ∀ X0 : G, (σ (M.op y y)) = (σ (k X0 y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ X0) = (σ y) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1151385 X0
       have i₂ := eq8406 y
       grind)
    | exact superpose eq8406 eq1151385
    | (have j0 := eq1151385 X0
       grind)
    | exact resolve eq1151385 eq8406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151385
  have eq1151574 : ∀ X0 : G, (σ y) = (σ (k X0 y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ X0) = (σ y) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1151483 X0
       have i₂ := eq691862
       grind)
    | exact superpose eq691862 eq1151483
    | (have j0 := eq1151483 X0
       grind)
    | exact resolve eq1151483 eq691862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151483
  have eq1151607 : ∀ X0 : G, (σ X0) = (M.op (σ y) (σ y)) ∨ (σ X0) = (σ y) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1151574 X0
       have j1 := eq1151230 X0
       grind)
    | (have r₁ := eq1151574 X0
       have r₂ := eq1151230 X0
       grind)
    | (have r₁ := eq1151574 (k X0 y)
       have r₂ := eq1151230 X0
       grind)
    | exact resolve eq1151574 eq1151230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151230 eq1151574
  have eq1151634 : ∀ X0 : G, (σ X0) = (σ (k y y)) ∨ (σ X0) = (σ y) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1151607 X0
       have i₂ := eq8152 y
       grind)
    | exact superpose eq8152 eq1151607
    | (have j0 := eq1151607 X0
       grind)
    | exact resolve eq1151607 eq8152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151607
  have eq1151646 : ∀ X0 : G, (σ X0) = (σ (M.op y y)) ∨ (σ X0) = (σ y) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1151634 X0
       have i₂ := eq8406 y
       grind)
    | exact superpose eq8406 eq1151634
    | (have j0 := eq1151634 X0
       grind)
    | exact resolve eq1151634 eq8406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151634
  have eq1151656 : ∀ X0 : G, (σ X0) = (σ y) ∨ (σ X0) = (σ y) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1151646 X0
       have i₂ := eq691862
       grind)
    | exact superpose eq691862 eq1151646
    | (have j0 := eq1151646 X0
       grind)
    | exact resolve eq1151646 eq691862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151646
  have eq1151657 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq1151656 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151656
  have eq1151842 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1151657 x
       grind)
    | exact superpose eq1151657 eq16
    | (have j1 := eq1151657 x
       grind)
    | exact resolve eq16 eq1151657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151657
  have eq1156483 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1151842
       have i₂ := eq508 x y
       grind)
    | exact superpose eq508 eq1151842
    | (have j1 := eq508 x y
       grind)
    | (have r₁ := eq1151842
       have r₂ := eq508 x y
       grind)
    | exact resolve eq1151842 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq1156484 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq1156483
  have eq1156488 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1156484
       have i₂ := eq691862
       grind)
    | exact superpose eq691862 eq1156484
    | exact resolve eq1156484 eq691862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156484
  have eq1160830 : y ≠ y ∨ (k x y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1156488
       grind)
    | exact superpose eq1156488 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1156488
       grind)
    | exact resolve eq13 eq1156488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1161005 : (k x y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1160830
  have eq1161041 : y = (k x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1161005
       have i₂ := eq691862
       grind)
    | exact superpose eq691862 eq1161005
    | exact resolve eq1161005 eq691862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161005
  have eq1161052 : x = y ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1161041
       have i₂ := eq691862
       grind)
    | exact superpose eq691862 eq1161041
    | exact resolve eq1161041 eq691862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691862 eq1161041
  have eq1161053 : y = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1161052
  have eq1161058 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1151842
       have i₂ := eq1161053
       grind)
    | exact superpose eq1161053 eq1151842
    | exact resolve eq1151842 eq1161053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151842 eq1161053
  have eq1161161 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1161058
  have eq1167393 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1161161
       have i₂ := eq1156488
       grind)
    | exact superpose eq1156488 eq1161161
    | exact resolve eq1161161 eq1156488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156488 eq1161161
  have eq1167399 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1167393
  have eq1167400 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1167399
  have eq1167401 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1167400
       grind)
    | exact superpose eq1167400 eq16
    | exact resolve eq16 eq1167400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167400
  have eq1167645 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1167401
       have i₂ := eq8152 x
       grind)
    | exact superpose eq8152 eq1167401
    | exact resolve eq1167401 eq8152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167401
  have eq1167647 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1167645
       have i₂ := eq8406 x
       grind)
    | exact superpose eq8406 eq1167645
    | exact resolve eq1167645 eq8406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167645
  have eq1167648 : (σ x) = (σ y) := by grind
  clear eq1167647
  have eq1170056 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1167648
       grind)
    | exact superpose eq1167648 eq16
    | exact resolve eq16 eq1167648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1170083 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1167648
       grind)
    | exact superpose eq1167648 eq10
    | exact resolve eq10 eq1167648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167648
  have eq1171202 : x = y := by
    first
    | (have i₁ := eq1170083
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1170083
    | exact resolve eq1170083 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170083
  have eq1171209 : (σ (M.op x y)) ≠ (σ (k x x)) := by
    first
    | (have i₁ := eq1170056
       have i₂ := eq8152 x
       grind)
    | exact superpose eq8152 eq1170056
    | exact resolve eq1170056 eq8152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8152 eq1170056
  have eq1171586 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1171209
       have i₂ := eq8406 x
       grind)
    | exact superpose eq8406 eq1171209
    | exact resolve eq1171209 eq8406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8406 eq1171209
  have eq1171882 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1171586
       have i₂ := eq1171202
       grind)
    | exact superpose eq1171202 eq1171586
    | exact resolve eq1171586 eq1171202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171202 eq1171586
  have eq1171883 : False := by grind
  exact eq1171883

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_x_pyx_Equation422 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law422 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq25
  have eq86 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq87 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq31
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq31 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq86 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1034 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq209 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq209
    | (have j0 := eq209 (σ X1) (σ X0)
       grind)
    | exact resolve eq209 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq7816 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq87 X1 X0
       grind)
    | exact superpose eq87 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq87 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq87 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq87 (σ X1) X1
       grind)
    | exact resolve eq13 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7859 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq87 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq7860 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq7859 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7859
  have eq7862 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq7816 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7816
  have eq7863 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq7862 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7862
  have eq7865 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq7860 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7860
    | (have j0 := eq7860 X0
       grind)
    | exact resolve eq7860 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7860
  have eq8045 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq7865 X0
       grind)
    | exact superpose eq7865 eq39
    | (have j1 := eq7865 X0
       grind)
    | exact resolve eq39 eq7865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq7865
  have eq8085 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq8045 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8045
    | (have j0 := eq8045 X0
       grind)
    | exact resolve eq8045 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8045
  have eq8086 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq8085 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8085
  have eq8091 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8086 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8086
    | exact resolve eq8086 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8126 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq8086 X0
       grind)
    | exact superpose eq8086 eq11
    | exact resolve eq11 eq8086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8086
  have eq8200 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8091 X0
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq8091
    | exact resolve eq8091 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8091
  have eq8317 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq8200 X0
       grind)
    | exact superpose eq8200 eq11
    | exact resolve eq11 eq8200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8200
  have eq8432 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq8317 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq8317
    | exact resolve eq8317 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8317
  have eq8972 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq9051 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq8972 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq8972
    | exact resolve eq8972 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8972
  have eq9107 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9051 X0
       have i₂ := eq8432 X0
       grind)
    | exact superpose eq8432 eq9051
    | exact resolve eq9051 eq8432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9051
  have eq9147 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq9107
  have eq38364 : ∀ X0 X1 : G, (σ (σ (τ X0))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1034 (τ X0) (τ X1)
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq1034
    | (have j0 := eq1034 (τ X0) (τ X1)
       grind)
    | exact resolve eq1034 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034
  have eq38462 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X0))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq38364 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq38364
    | (have j0 := eq38364 X0 X1
       grind)
    | exact resolve eq38364 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38364
  have eq38526 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq38462 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq38462
    | (have j0 := eq38462 X0 X1
       grind)
    | exact resolve eq38462 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38462
  have eq38589 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (σ (τ X1))) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq38526 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq38526
    | (have j0 := eq38526 X0 X1
       grind)
    | exact resolve eq38526 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38526
  have eq38647 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq38589 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq38589
    | (have j0 := eq38589 X0 X1
       grind)
    | exact resolve eq38589 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38589
  have eq38698 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) (σ (τ X1)))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38647 X0 X1
       have i₂ := eq8126 (σ (τ X1))
       grind)
    | exact superpose eq8126 eq38647
    | (have j0 := eq38647 X0 X1
       grind)
    | exact resolve eq38647 eq8126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38647
  have eq38747 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (σ (k (τ X1) (τ X1)))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38698 X0 X1
       have i₂ := eq15 (τ X1) (τ X1)
       grind)
    | exact superpose eq15 eq38698
    | (have j0 := eq38698 X0 X1
       grind)
    | exact resolve eq38698 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38698
  have eq38792 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38747 X0 X1
       have i₂ := eq19 X1 (τ X1)
       grind)
    | exact superpose eq19 eq38747
    | (have j0 := eq38747 X0 X1
       grind)
    | exact resolve eq38747 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38747
  have eq38832 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k X1 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38792 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq38792
    | (have j0 := eq38792 X0 X1
       grind)
    | exact resolve eq38792 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38792
  have eq38863 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38832 X0 X1
       have i₂ := eq8432 X1
       grind)
    | exact superpose eq8432 eq38832
    | (have j0 := eq38832 X0 X1
       grind)
    | exact resolve eq38832 eq8432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38832
  have eq38888 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38863 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq38863
    | (have j0 := eq38863 X0 X1
       grind)
    | exact resolve eq38863 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38863
  have eq45590 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq7863 X0 X1
       grind)
    | exact superpose eq7863 eq31
    | (have j1 := eq7863 X0 X1
       grind)
    | exact resolve eq31 eq7863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq7863
  have eq45826 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq45590 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45590
    | (have j0 := eq45590 X0 X1
       grind)
    | exact resolve eq45590 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45590
  have eq48154 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X0) = (k (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq45826 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq45826
    | (have j0 := eq45826 (τ X0) X1
       grind)
    | exact resolve eq45826 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48221 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 (σ X0))
       have i₂ := eq45826 X0 X1
       grind)
    | exact superpose eq45826 eq11
    | (have j1 := eq45826 X0 X1
       grind)
    | exact resolve eq11 eq45826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45826
  have eq48356 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq48221 X0 X1
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq48221
    | (have j0 := eq48221 X0 X1
       grind)
    | exact resolve eq48221 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq48221
  have eq48395 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X0) = (k (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq48154 X0 X1
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq48154
    | (have j0 := eq48154 X0 X1
       grind)
    | exact resolve eq48154 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48154
  have eq48435 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq48395 X0 X1
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq48395
    | (have j0 := eq48395 X0 X1
       grind)
    | exact resolve eq48395 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq48395
  have eq49578 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq48356 X1 (σ X0)
       grind)
    | exact superpose eq48356 eq15
    | (have j1 := eq48356 X1 (σ X0)
       grind)
    | exact resolve eq15 eq48356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48356
  have eq49738 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 (τ (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49578 X0 X1
       have i₂ := eq8126 X0
       grind)
    | exact superpose eq8126 eq49578
    | (have j0 := eq49578 X0 X1
       grind)
    | exact resolve eq49578 eq8126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8126 eq49578
  have eq49803 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 (τ (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49738 X0 X1
       have i₂ := eq8432 X0
       grind)
    | exact superpose eq8432 eq49738
    | (have j0 := eq49738 X0 X1
       grind)
    | exact resolve eq49738 eq8432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8432 eq49738
  have eq49851 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49803 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq49803
    | (have j0 := eq49803 X0 X1
       grind)
    | exact resolve eq49803 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49803
  have eq51529 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X1 X0)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq48435 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48435
  have eq58254 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq49851 x y
       grind)
    | exact superpose eq49851 eq16
    | (have j1 := eq49851 x y
       grind)
    | exact resolve eq16 eq49851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49851
  have eq58843 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq58254
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq58254
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq58254 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58254
  have eq58849 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq58843
  have eq58850 : y = (M.op x y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq58849
  have eq59376 : (τ y) ≠ (τ y) ∨ (τ (k y x)) = (τ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq51529 y x
       have i₂ := eq58850
       grind)
    | exact superpose eq58850 eq51529
    | (have j0 := eq51529 y x
       grind)
    | exact resolve eq51529 eq58850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51529
  have eq59377 : (τ y) ≠ (τ y) ∨ (τ (k y x)) = (τ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq59376
  have eq59378 : y = (M.op x x) ∨ (τ (k y x)) = (τ y) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq59377
  have eq59938 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ (k y x)) = (τ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9147 x
       have i₂ := eq59378
       grind)
    | exact superpose eq59378 eq9147
    | exact resolve eq9147 eq59378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59378
  have eq59995 : (σ y) = (σ (M.op x x)) ∨ (τ (k y x)) = (τ y) := by
    first
    | (have r₁ := eq59938
       have r₂ := eq16
       grind)
    | exact resolve eq59938 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59938
  have eq60472 : (M.op x x) = (τ (σ y)) ∨ (τ (k y x)) = (τ y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq59995
       grind)
    | exact superpose eq59995 eq10
    | exact resolve eq10 eq59995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59995
  have eq60619 : y = (M.op x x) ∨ (τ (k y x)) = (τ y) := by
    first
    | (have i₁ := eq60472
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq60472
    | exact resolve eq60472 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60472
  have eq60714 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ (k y x)) = (τ y) := by
    first
    | (have i₁ := eq9147 x
       have i₂ := eq60619
       grind)
    | exact superpose eq60619 eq9147
    | exact resolve eq9147 eq60619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60619
  have eq60771 : (τ (k y x)) = (τ y) := by
    first
    | (have r₁ := eq60714
       have r₂ := eq16
       grind)
    | exact resolve eq60714 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60714
  have eq60888 : (k y x) = (σ (τ y)) := by
    first
    | (have i₁ := eq11 (k y x)
       have i₂ := eq60771
       grind)
    | exact superpose eq60771 eq11
    | exact resolve eq11 eq60771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60771
  have eq61101 : y = (k y x) := by
    first
    | (have i₁ := eq60888
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq60888
    | exact resolve eq60888 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60888
  have eq61180 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq38888 y x
       have i₂ := eq61101
       grind)
    | exact superpose eq61101 eq38888
    | (have j0 := eq38888 y x
       grind)
    | exact resolve eq38888 eq61101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38888 eq61101
  have eq61183 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq61180
  have eq70886 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq61183
       grind)
    | exact superpose eq61183 eq16
    | exact resolve eq16 eq61183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61183
  have eq71498 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq70886
       have i₂ := eq58850
       grind)
    | exact superpose eq58850 eq70886
    | exact resolve eq70886 eq58850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58850 eq70886
  have eq71499 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq71498
  have eq71500 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq71499
  have eq71520 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9147 x
       have i₂ := eq71500
       grind)
    | exact superpose eq71500 eq9147
    | exact resolve eq9147 eq71500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71500
  have eq71588 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq71520
       have r₂ := eq16
       grind)
    | exact resolve eq71520 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71520
  have eq72551 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq71588
       grind)
    | exact superpose eq71588 eq10
    | exact resolve eq10 eq71588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71588
  have eq72716 : y = (M.op x x) := by
    first
    | (have i₁ := eq72551
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq72551
    | exact resolve eq72551 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72551
  have eq72866 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9147 x
       have i₂ := eq72716
       grind)
    | exact superpose eq72716 eq9147
    | exact resolve eq9147 eq72716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9147 eq72716
  have eq72934 : False := by grind
  exact eq72934

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyy_pxy_Equation422 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law422 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq21 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq21 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq26 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq26 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq38 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq34 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq36 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq37 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq37 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq38 X1 X0
       grind)
    | (have r₁ := eq42 X1 X0
       have r₂ := eq38 X0 X1
       grind)
    | exact resolve eq42 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq42
  have eq47 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq45
  have eq94 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq39 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq98 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq94 X0 X1
       have j1 := eq47 X0 X1
       grind)
    | (have r₁ := eq94 X0 X1
       have r₂ := eq47 X0 X1
       grind)
    | (have r₁ := eq94 X1 X1
       have r₂ := eq47 X1 X1
       grind)
    | exact resolve eq94 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq94
  have eq237 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq98 (σ X0) (σ X1)
       grind)
    | exact superpose eq98 eq15
    | exact resolve eq15 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq237 X0 X1
       have i₂ := eq98 X0 X1
       grind)
    | exact superpose eq98 eq237
    | exact resolve eq237 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq237
  have eq247 : False := by grind
  exact eq247

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_y_pxy_Equation422 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law422 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq42 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X2 X0))) = (M.op (M.op X0 (M.op X1 (M.op X2 X0))) (M.op (M.op X0 (M.op X1 (M.op X2 X0))) (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 (M.op X1 (M.op X2 X0))) X3 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X2 X0)) X0 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (σ X0) = (k X1 (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq97 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
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
  have eq98 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq95
    | (have j0 := eq95 X0 X1
       grind)
    | exact resolve eq95 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq127 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op X3 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq43 (M.op X0 (M.op X1 (M.op X2 X0))) X1 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq43
    | exact resolve eq43 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq201 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq98 x y
       grind)
    | exact superpose eq98 eq16
    | (have j1 := eq98 x y
       grind)
    | exact resolve eq16 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq98 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X0))) (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X0)))))) = (M.op (M.op (M.op X0 (M.op X1 (M.op X2 X0))) (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X0)))))) (M.op (M.op (M.op X0 (M.op X1 (M.op X2 X0))) (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X0)))))) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq42 (M.op X0 (M.op X1 (M.op X2 X0))) X3 X4 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq42
    | exact resolve eq42 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq378 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 (M.op (M.op X0 (M.op X1 (M.op X2 X0))) (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X0)))))))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq127 (M.op X0 (M.op X1 (M.op X2 X0))) X0 X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq127
    | exact resolve eq127 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383 : ∀ X0 X1 X2 X3 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (M.op (σ (k X0 X1)) (M.op (σ X1) (M.op X2 (M.op X3 (σ X1)))))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq127 (σ X1) (σ X0) X2 X3
       have i₂ := eq98 X0 X1
       grind)
    | exact superpose eq98 eq127
    | (have j1 := eq98 X0 X1
       grind)
    | exact resolve eq127 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq885 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq97 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq97
    | exact resolve eq97 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq932 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq885 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq885
    | (have j0 := eq885 X0 X1
       grind)
    | exact resolve eq885 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885
  have eq1817 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq201
       have i₂ := eq932 x y
       grind)
    | exact superpose eq932 eq201
    | (have j1 := eq932 x y
       grind)
    | (have r₁ := eq201
       have r₂ := eq932 x y
       grind)
    | (have r₁ := eq201
       have r₂ := eq932 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq201
       have r₂ := eq932 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq201 eq932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932
  have eq1818 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq1817
  have eq7598 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X5 X0) = (M.op (M.op X5 X0) (M.op (M.op X5 X0) (M.op X0 (M.op (M.op X0 (M.op X1 (M.op X2 X0))) (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X0))))))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq127 X0 X5 (M.op (M.op X0 (M.op X1 (M.op X2 X0))) (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X0)))))) (M.op (M.op X0 (M.op X1 (M.op X2 X0))) (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X0))))))
       have i₂ := eq302 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq302 eq127
    | exact resolve eq127 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq302
  have eq20750 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1818
       grind)
    | exact superpose eq1818 eq16
    | exact resolve eq16 eq1818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1818
  have eq20751 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq20750
       have r₂ := eq22 x
       grind)
    | exact resolve eq20750 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20750
  have eq20995 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq60 y (σ x)
       have i₂ := eq20751
       grind)
    | exact superpose eq20751 eq60
    | (have j0 := eq60 y (σ x)
       grind)
    | (have r₁ := eq60 y (σ x)
       have r₂ := eq20751
       grind)
    | exact resolve eq60 eq20751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20751
  have eq21024 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq20995
  have eq21025 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq21024
  have eq21030 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq21025
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq21025
    | exact resolve eq21025 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21025
  have eq21032 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = (k X0 y) ∨ y = X0 ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq21030
       grind)
    | exact superpose eq21030 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq21030
       grind)
    | exact resolve eq13 eq21030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21030
  have eq72307 : x = y ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have j0 := eq21032 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21032
  have eq72820 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq72307
       grind)
    | exact superpose eq72307 eq16
    | exact resolve eq16 eq72307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72307
  have eq72821 : y = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq72820
       have r₂ := eq22 x
       grind)
    | exact resolve eq72820 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72820
  have eq72822 : x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq72821
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq72821
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq72821 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72827 : (σ y) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq205 x y
       have i₂ := eq72821
       grind)
    | exact superpose eq72821 eq205
    | (have j0 := eq205 x y
       grind)
    | exact resolve eq205 eq72821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72903 : (σ y) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq72827
  have eq98545 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq72822
       grind)
    | exact superpose eq72822 eq16
    | exact resolve eq16 eq72822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72822
  have eq98546 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq98545
       have r₂ := eq22 x
       grind)
    | exact resolve eq98545 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98545
  have eq98578 : ∀ X0 X1 X2 X3 : G, y = (M.op y (M.op y (M.op y (M.op (M.op y (M.op X0 (M.op X1 y))) (M.op X2 (M.op X3 (M.op y (M.op X0 (M.op X1 y))))))))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7598 y X1 X2 X3 x x
       have i₂ := eq98546
       grind)
    | exact superpose eq98546 eq7598
    | exact resolve eq7598 eq98546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98590 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq98578 x x x x
       have i₂ := eq378 y x x x x
       grind)
    | exact superpose eq378 eq98578
    | exact resolve eq98578 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98578
  have eq98874 : y ≠ (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq98590
  have eq98877 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq98874
       have r₂ := eq98546
       grind)
    | exact resolve eq98874 eq98546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98546 eq98874
  have eq98887 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = (k X0 y) ∨ y = X0 ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq98877
       grind)
    | exact superpose eq98877 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq98877
       grind)
    | exact resolve eq13 eq98877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105275 : x = y ∨ y = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have j0 := eq98887 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98887
  have eq105276 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq105275
       grind)
    | exact superpose eq105275 eq16
    | exact resolve eq16 eq105275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105275
  have eq105277 : y = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq105276
       have r₂ := eq22 x
       grind)
    | exact resolve eq105276 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105276
  have eq105527 : (σ y) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq205 x y
       have i₂ := eq105277
       grind)
    | exact superpose eq105277 eq205
    | (have j0 := eq205 x y
       grind)
    | exact resolve eq205 eq105277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq105632 : (σ y) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq105527
  have eq115849 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op X0 (M.op X1 (σ y)))))) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq383 x y x x
       have i₂ := eq105277
       grind)
    | exact superpose eq105277 eq383
    | (have j0 := eq383 x y x x
       grind)
    | exact resolve eq383 eq105277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105277
  have eq115850 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op X0 (M.op X1 (σ y)))))) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq383 x y x x
       have i₂ := eq72821
       grind)
    | exact superpose eq72821 eq383
    | (have j0 := eq383 x y x x
       grind)
    | exact resolve eq383 eq72821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383 eq72821
  have eq116105 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op X0 (M.op X1 (σ y)))))) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    intro X0 X1
    first
    | (have j0 := eq115850 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115850
  have eq116106 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op X0 (M.op X1 (σ y)))))) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have j0 := eq115849 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115849
  have eq116219 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq116105 x x
       have i₂ := eq9 (σ y) x x
       grind)
    | exact superpose eq9 eq116105
    | exact resolve eq116105 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116105
  have eq116220 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq116106 x x
       have i₂ := eq9 (σ y) x x
       grind)
    | exact superpose eq9 eq116106
    | exact resolve eq116106 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116106
  have eq116335 : (σ y) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq116219
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq116219
    | exact resolve eq116219 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116219
  have eq116336 : (σ y) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq116220
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq116220
    | exact resolve eq116220 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116220
  have eq116413 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq116335
       have r₂ := eq72903
       grind)
    | exact resolve eq116335 eq72903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72903 eq116335
  have eq116414 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq116336
       have r₂ := eq105632
       grind)
    | exact resolve eq116336 eq105632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105632 eq116336
  have eq119614 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq60 y (σ x)
       have i₂ := eq116413
       grind)
    | exact superpose eq116413 eq60
    | (have j0 := eq60 y (σ x)
       grind)
    | (have r₁ := eq60 y (σ x)
       have r₂ := eq116413
       grind)
    | exact resolve eq60 eq116413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq116413
  have eq119670 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq119614
  have eq119671 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq119670
  have eq119680 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq119671
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq119671
    | exact resolve eq119671 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119671
  have eq119681 : (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq119680
  have eq120101 : y = (τ (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq119681
       grind)
    | exact superpose eq119681 eq10
    | exact resolve eq10 eq119681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119681
  have eq120337 : x = y ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq120101
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq120101
    | exact resolve eq120101 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120101
  have eq120339 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq120337
       grind)
    | exact superpose eq120337 eq16
    | exact resolve eq16 eq120337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120337
  have eq120340 : (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq120339
       have r₂ := eq22 x
       grind)
    | exact resolve eq120339 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120339
  have eq120752 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq201
       have i₂ := eq120340
       grind)
    | exact superpose eq120340 eq201
    | exact resolve eq201 eq120340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201 eq120340
  have eq121018 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq120752
       have r₂ := eq116414
       grind)
    | exact resolve eq120752 eq116414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116414 eq120752
  have eq126701 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq121018
       grind)
    | exact superpose eq121018 eq16
    | exact resolve eq16 eq121018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121018
  have eq127532 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq126701
       have i₂ := eq98877
       grind)
    | exact superpose eq98877 eq126701
    | exact resolve eq126701 eq98877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98877
  have eq127539 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq127532
  have eq127540 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq127539
  have eq127542 : (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq127540
       grind)
    | exact superpose eq127540 eq10
    | exact resolve eq10 eq127540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127788 : y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq127542
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq127542
    | exact resolve eq127542 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127542
  have eq128553 : ∀ X0 X1 X2 X3 : G, y = (M.op y (M.op y (M.op y (M.op (M.op y (M.op X0 (M.op X1 y))) (M.op X2 (M.op X3 (M.op y (M.op X0 (M.op X1 y))))))))) ∨ (σ x) = (σ y) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7598 y X1 X2 X3 x x
       have i₂ := eq127788
       grind)
    | exact superpose eq127788 eq7598
    | exact resolve eq7598 eq127788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7598 eq127788
  have eq128571 : y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq128553 x x x x
       have i₂ := eq378 y x x x x
       grind)
    | exact superpose eq378 eq128553
    | exact resolve eq128553 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq128553
  have eq128583 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq126701
       have i₂ := eq128571
       grind)
    | exact superpose eq128571 eq126701
    | exact resolve eq126701 eq128571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126701 eq128571
  have eq128667 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq128583
  have eq128679 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq128667
       have r₂ := eq127540
       grind)
    | exact resolve eq128667 eq127540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127540 eq128667
  have eq129436 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq128679
       grind)
    | exact superpose eq128679 eq16
    | exact resolve eq16 eq128679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129437 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq128679
       grind)
    | exact superpose eq128679 eq10
    | exact resolve eq10 eq128679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128679
  have eq129686 : x = y := by
    first
    | (have i₁ := eq129437
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq129437
    | exact resolve eq129437 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129437
  have eq129687 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq129436
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq129436
    | exact resolve eq129436 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq129436
  have eq129688 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq129687
       have i₂ := eq129686
       grind)
    | exact superpose eq129686 eq129687
    | exact resolve eq129687 eq129686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129686 eq129687
  have eq129689 : False := by grind
  exact eq129689

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxy_pxx_pyx_Equation422 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law422 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq63 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq106 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (M.op X1 (σ (M.op X0 X0))))) := by
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
  have eq109 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X2 X0)) X0 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq115 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq117 : ∀ X0 X1 : G, (τ X1) = (M.op X0 (τ X1)) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq505 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op X3 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq109 (M.op X0 (M.op X1 (M.op X2 X0))) X1 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq109
    | exact resolve eq109 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq702 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq115 x y
       grind)
    | exact superpose eq115 eq16
    | (have j1 := eq115 x y
       grind)
    | exact resolve eq16 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq711 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq115 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq722 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq114 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq114
    | exact resolve eq114 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq771 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq722 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq722
    | (have j0 := eq722 X0 X1
       grind)
    | exact resolve eq722 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq828 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq711 (τ X1) (τ X0)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq711
    | (have j0 := eq711 (τ X1) (τ X0)
       grind)
    | exact resolve eq711 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq711
  have eq836 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq828 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq828
    | (have j0 := eq828 X0 X1
       grind)
    | exact resolve eq828 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq839 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq836 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq836
    | (have j0 := eq836 X0 X1
       grind)
    | exact resolve eq836 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq841 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq839 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq839
    | (have j0 := eq839 X0 X1
       grind)
    | exact resolve eq839 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq842 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq841 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq841
    | (have j0 := eq841 X0 X1
       grind)
    | exact resolve eq841 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq843 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq842 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq842
    | (have j0 := eq842 X0 X1
       grind)
    | exact resolve eq842 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq844 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq843 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq843
    | (have j0 := eq843 X0 X1
       grind)
    | exact resolve eq843 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq3661 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq117 X1 X0
       grind)
    | exact superpose eq117 eq13
    | (have j0 := eq13 (τ X0) X1
       have j1 := eq117 X1 X0
       grind)
    | (have r₁ := eq13 (τ X1) X0
       have r₂ := eq117 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) X1
       have r₂ := eq117 (M.op X1 (τ X1)) X1
       grind)
    | exact resolve eq13 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq3665 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq3661 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3661
  have eq3666 : ∀ X0 X1 : G, (τ X0) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq3665 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3665
  have eq3668 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3666 X0 X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq3666
    | (have j0 := eq3666 X0 X1
       grind)
    | exact resolve eq3666 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq3666
  have eq6424 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq702
       have i₂ := eq771 x y
       grind)
    | exact superpose eq771 eq702
    | (have j1 := eq771 (σ x) (σ y)
       grind)
    | (have r₁ := eq702
       have r₂ := eq771 x y
       grind)
    | (have r₁ := eq702
       have r₂ := eq771 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq702
       have r₂ := eq771 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq702 eq771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq6425 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq6424
  have eq6829 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6425
       grind)
    | exact superpose eq6425 eq16
    | exact resolve eq16 eq6425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6425
  have eq6830 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq6829
       have r₂ := eq22 x
       grind)
    | exact resolve eq6829 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6829
  have eq6836 : ∀ X0 X1 : G, y = (M.op y (M.op y (M.op y (M.op X0 (M.op X1 y))))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq505 y x x x
       have i₂ := eq6830
       grind)
    | exact superpose eq6830 eq505
    | exact resolve eq505 eq6830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6830
  have eq6840 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq6836 x x
       have i₂ := eq9 y x x
       grind)
    | exact superpose eq9 eq6836
    | exact resolve eq6836 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6836
  have eq6848 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op X0 (M.op X1 (σ y)))))) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq505 (σ y) (σ x) x x
       have i₂ := eq6840
       grind)
    | exact superpose eq6840 eq505
    | exact resolve eq505 eq6840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505 eq6840
  have eq6854 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq6848 x x
       have i₂ := eq9 (σ y) x x
       grind)
    | exact superpose eq9 eq6848
    | exact resolve eq6848 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6848
  have eq6857 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq6854
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq6854
    | exact resolve eq6854 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6854
  have eq6863 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6857
       grind)
    | exact superpose eq6857 eq10
    | exact resolve eq10 eq6857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6857
  have eq6914 : x = y ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq6863
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6863
    | exact resolve eq6863 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6863
  have eq6916 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6914
       grind)
    | exact superpose eq6914 eq16
    | exact resolve eq16 eq6914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6914
  have eq6917 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq6916
       have r₂ := eq22 x
       grind)
    | exact resolve eq6916 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6916
  have eq6920 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op X0 (σ y)))) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq106 y X0
       have i₂ := eq6917
       grind)
    | exact superpose eq6917 eq106
    | exact resolve eq106 eq6917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq6917
  have eq7369 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 (σ y) (σ y) x
       have i₂ := eq6920 x
       grind)
    | exact superpose eq6920 eq9
    | exact resolve eq9 eq6920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6920
  have eq7383 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq7369
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq7369
    | exact resolve eq7369 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7369
  have eq7384 : (σ y) = (σ (M.op y y)) := by grind
  clear eq7383
  have eq7398 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq7384
       grind)
    | exact superpose eq7384 eq10
    | exact resolve eq10 eq7384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7399 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (k (M.op y y) X0)) := by
    intro X0
    first
    | (have i₁ := eq15 (M.op y y) X0
       have i₂ := eq7384
       grind)
    | exact superpose eq7384 eq15
    | exact resolve eq15 eq7384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7448 : ∀ X0 : G, (σ (k y X0)) = (σ (k (M.op y y) X0)) := by
    intro X0
    first
    | (have i₁ := eq7399 X0
       have i₂ := eq15 y X0
       grind)
    | exact superpose eq15 eq7399
    | exact resolve eq7399 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7399
  have eq7449 : y = (M.op y y) := by
    first
    | (have i₁ := eq7398
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq7398
    | exact resolve eq7398 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7398
  have eq26627 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3668 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3668
    | (have j0 := eq3668 (M.op (σ X0) (σ X0)) (k X0 X1)
       grind)
    | exact resolve eq3668 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3668
  have eq26732 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq26627 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq26627
    | (have j0 := eq26627 X0 X1
       grind)
    | exact resolve eq26627 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26627
  have eq26739 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26732 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq26732
    | (have j0 := eq26732 X0 X1
       grind)
    | exact resolve eq26732 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26732
  have eq26743 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26739 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq26739
    | (have j0 := eq26739 X0 X1
       grind)
    | exact resolve eq26739 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26739
  have eq26838 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 (M.op y y))) ∨ (M.op (M.op y y) (M.op y y)) = (k (M.op y y) X0) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq7448 X0
       have i₂ := eq26743 (M.op y y) X0
       grind)
    | exact superpose eq26743 eq7448
    | (have j1 := eq26743 (M.op y y) X0
       grind)
    | exact resolve eq7448 eq26743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7448 eq26743
  have eq26936 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ (M.op (M.op y y) (M.op y y)) = (k (M.op y y) X0) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq26838 X0
       have i₂ := eq7449
       grind)
    | exact superpose eq7449 eq26838
    | (have j0 := eq26838 X0
       grind)
    | exact resolve eq26838 eq7449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26838
  have eq26983 : ∀ X0 : G, (M.op y y) = (k y X0) ∨ (σ (k y X0)) = (σ (M.op X0 y)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq26936 X0
       have i₂ := eq7449
       grind)
    | exact superpose eq7449 eq26936
    | (have j0 := eq26936 X0
       grind)
    | exact resolve eq26936 eq7449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26936
  have eq27015 : ∀ X0 : G, y = (k y X0) ∨ (σ (k y X0)) = (σ (M.op X0 y)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq26983 X0
       have i₂ := eq7449
       grind)
    | exact superpose eq7449 eq26983
    | (have j0 := eq26983 X0
       grind)
    | exact resolve eq26983 eq7449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26983
  have eq27032 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ y = (k y X0) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq27015 X0
       have i₂ := eq7449
       grind)
    | exact superpose eq7449 eq27015
    | (have j0 := eq27015 X0
       grind)
    | exact resolve eq27015 eq7449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7449 eq27015
  have eq27597 : ∀ X0 : G, (k y X0) = (τ (σ (M.op X0 y))) ∨ y = (k y X0) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k y X0)
       have i₂ := eq27032 X0
       grind)
    | exact superpose eq27032 eq10
    | (have j1 := eq27032 X0
       grind)
    | exact resolve eq10 eq27032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27032
  have eq27667 : ∀ X0 : G, y = (k y X0) ∨ (M.op X0 y) = (k y X0) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq27597 X0
       have i₂ := eq10 (M.op X0 y)
       grind)
    | exact superpose eq10 eq27597
    | (have j0 := eq27597 X0
       grind)
    | exact resolve eq27597 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27597
  have eq27781 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ (M.op X0 y) = (k y X0) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq27667 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27667
  have eq27820 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq27781 X0
       have j1 := eq14 y X0
       grind)
    | (have r₁ := eq27781 x
       have r₂ := eq14 y x
       grind)
    | (have r₁ := eq27781 X0
       have r₂ := eq14 y (M.op X0 y)
       grind)
    | (have r₁ := eq27781 X0
       have r₂ := eq14 (M.op X0 y) y
       grind)
    | exact resolve eq27781 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27781
  have eq27837 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq702
       have i₂ := eq27820 x
       grind)
    | exact superpose eq27820 eq702
    | (have j1 := eq27820 x
       grind)
    | exact resolve eq702 eq27820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq27820
  have eq27916 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq27837
  have eq28713 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq27916
       grind)
    | exact superpose eq27916 eq16
    | exact resolve eq16 eq27916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28725 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq27916
       grind)
    | exact superpose eq27916 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq27916
       grind)
    | exact resolve eq13 eq27916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27916
  have eq28739 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq28725
  have eq28740 : (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq28739
  have eq28750 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq28740
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq28740
    | exact resolve eq28740 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28740
  have eq28765 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq28750
       have i₂ := eq7384
       grind)
    | exact superpose eq7384 eq28750
    | exact resolve eq28750 eq7384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7384 eq28750
  have eq28769 : (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq28765
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq28765
    | exact resolve eq28765 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28765
  have eq29192 : y = (τ (σ x)) ∨ (σ y) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq28769
       grind)
    | exact superpose eq28769 eq10
    | exact resolve eq10 eq28769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28769
  have eq29267 : x = y ∨ (σ y) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq29192
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq29192
    | exact resolve eq29192 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29192
  have eq29268 : (σ y) = (σ (k y x)) ∨ x = y := by grind
  clear eq29267
  have eq29298 : (k y x) = (τ (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq29268
       grind)
    | exact superpose eq29268 eq10
    | exact resolve eq10 eq29268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29268
  have eq29381 : y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq29298
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq29298
    | exact resolve eq29298 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29298
  have eq29413 : y ≠ y ∨ y = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq844 y x
       have i₂ := eq29381
       grind)
    | exact superpose eq29381 eq844
    | (have j0 := eq844 y x
       grind)
    | (have r₁ := eq844 y x
       have r₂ := eq29381
       grind)
    | exact resolve eq844 eq29381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844 eq29381
  have eq29449 : y ≠ y ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq29413
  have eq29450 : y = (M.op x y) ∨ x = y := by grind
  clear eq29449
  have eq29472 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq28713
       have i₂ := eq29450
       grind)
    | exact superpose eq29450 eq28713
    | exact resolve eq28713 eq29450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28713 eq29450
  have eq29519 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq29472
  have eq29520 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq29519
  have eq29553 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq29520
       grind)
    | exact superpose eq29520 eq10
    | exact resolve eq10 eq29520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29520
  have eq29628 : x = y ∨ x = y := by
    first
    | (have i₁ := eq29553
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq29553
    | exact resolve eq29553 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29553
  have eq29629 : x = y := by grind
  clear eq29628
  have eq29636 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29629
       grind)
    | exact superpose eq29629 eq16
    | exact resolve eq16 eq29629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29629
  have eq29727 : False := by grind
  exact eq29727

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation426 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law426 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
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
  have eq50 : x ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (k y x) := by
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
  have eq65 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq78 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq16
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq71
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq71 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq86
    | exact resolve eq86 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq94
    | exact resolve eq94 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq96 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq96
    | exact resolve eq96 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq641 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq642 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq641
    | exact resolve eq641 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq645 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq642
       have r₂ := eq27
       grind)
    | exact resolve eq642 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq647 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq645
    | exact resolve eq645 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq649 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq647
    | exact resolve eq647 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq651 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq649 eq65
    | (have r₁ := eq65
       have r₂ := eq649
       grind)
    | exact resolve eq65 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq654 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq649
  have eq655 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq651
  have eq699 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq655
       have r₂ := eq654
       grind)
    | exact resolve eq655 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654 eq655
  have eq703 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq699 eq78
    | exact resolve eq78 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq711 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq703
    | exact resolve eq703 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq703
  have eq715 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq711
       have r₂ := eq64
       grind)
    | exact resolve eq711 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq760 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq715
       grind)
    | exact superpose eq715 eq71
    | exact resolve eq71 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq761 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq715
       grind)
    | exact superpose eq715 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq762 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq761
  have eq764 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq762
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq762
    | exact resolve eq762 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq765 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq764
  have eq766 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq760
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq760
    | exact resolve eq760 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760
  have eq769 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq765
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq765
    | exact resolve eq765 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq772 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq769 eq51
    | (have r₁ := eq51
       have r₂ := eq769
       grind)
    | exact resolve eq51 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq774 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq772
  have eq822 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq766 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq823 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq822
  have eq827 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq823
    | exact resolve eq823 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq828 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq827
  have eq833 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq828
    | exact resolve eq828 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq838 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq833 eq27
    | exact resolve eq27 eq833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833
  have eq940 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq774 eq78
    | exact resolve eq78 eq774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq951 : y = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq940
    | exact resolve eq940 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq954 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq951
       have r₂ := eq50
       grind)
    | exact resolve eq951 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq960 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq954
       grind)
    | exact superpose eq954 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq961 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq960
  have eq963 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq961
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq961
    | exact resolve eq961 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961
  have eq964 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq963
  have eq968 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq964
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq964
    | exact resolve eq964 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq964
  have eq970 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq968 eq20
    | exact resolve eq20 eq968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq973 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq968 eq64
    | (have r₁ := eq64
       have r₂ := eq968
       grind)
    | exact resolve eq64 eq968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq982 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq968
  have eq983 : x = y ∨ x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq973
  have eq994 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq970
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq970
    | exact resolve eq970 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq1058 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq994 eq838
    | (have r₁ := eq838
       have r₂ := eq994
       grind)
    | exact resolve eq838 eq994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838 eq994
  have eq1061 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1058
  have eq1062 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1061
  have eq1129 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1062 eq51
    | (have r₁ := eq51
       have r₂ := eq1062
       grind)
    | exact resolve eq51 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1062
  have eq1130 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1129
  have eq1209 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1130 eq78
    | exact resolve eq78 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq1130
  have eq1224 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1209
    | exact resolve eq1209 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1209
  have eq1227 : y = (k y x) := by
    first
    | (have r₁ := eq1224
       have r₂ := eq50
       grind)
    | exact resolve eq1224 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1224
  have eq1281 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq1227
       grind)
    | exact superpose eq1227 eq71
    | exact resolve eq71 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq1286 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1281
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1281
    | exact resolve eq1281 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1281
  have eq1299 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1286 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1300 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1299
  have eq1302 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1300
    | exact resolve eq1300 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300
  have eq1305 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1302
    | exact resolve eq1302 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1302
  have eq1309 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1305 eq65
    | (have r₁ := eq65
       have r₂ := eq1305
       grind)
    | exact resolve eq65 eq1305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq1312 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1305
  have eq1313 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1309
  have eq1314 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1286 eq1313
    | exact resolve eq1313 eq1286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286 eq1313
  have eq1315 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1314
  have eq1425 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1315
       have r₂ := eq1312
       grind)
    | exact resolve eq1315 eq1312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312 eq1315
  have eq1429 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1425 eq27
    | exact resolve eq27 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1425
  have eq2521 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq983
       have r₂ := eq982
       grind)
    | exact resolve eq983 eq982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983
  have eq2522 : x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2521
       have i₂ := eq1227
       grind)
    | exact superpose eq1227 eq2521
    | exact resolve eq2521 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227 eq2521
  have eq2523 : x = (M.op x y) := by
    first
    | (have r₁ := eq2522
       have r₂ := eq982
       grind)
    | exact resolve eq2522 eq982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982 eq2522
  have eq2525 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2523 eq20
    | exact resolve eq20 eq2523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2523
  have eq2552 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2525
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2525
    | exact resolve eq2525 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2525
  have eq2554 : False := by grind
  exact eq2554

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation426 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law426 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq270 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq270 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq273 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq271 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq271 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq271 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq284 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq273 (σ X0)
       grind)
    | exact superpose eq273 eq15
    | exact resolve eq15 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq273 (τ X0)
       grind)
    | exact superpose eq273 eq31
    | exact resolve eq31 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq297 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq290 X0
       have i₂ := eq273 X0
       grind)
    | exact superpose eq273 eq290
    | exact resolve eq290 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq303 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq284 X0
       have i₂ := eq273 X0
       grind)
    | exact superpose eq273 eq284
    | exact resolve eq284 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273 eq284
  have eq347 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq303 X0
       grind)
    | exact superpose eq303 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq303 X0
       grind)
    | exact superpose eq303 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq352 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq347 X0 X1
       have j1 := eq349 X0 X1
       grind)
    | (have r₁ := eq347 X0 X1
       have r₂ := eq349 X0 X1
       grind)
    | exact resolve eq347 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347 eq349
  have eq365 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (τ X0)
       have i₂ := eq297 X0
       grind)
    | exact superpose eq297 eq14
    | (have j0 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq14 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq367 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq297 X0
       grind)
    | exact superpose eq297 eq12
    | (have j0 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq12 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq370 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq365 X0 X1
       have j1 := eq367 X0 X1
       grind)
    | (have r₁ := eq365 X0 X1
       have r₂ := eq367 X0 X1
       grind)
    | exact resolve eq365 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365 eq367
  have eq427 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq352 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq352
    | exact resolve eq352 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq458 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq427 (σ x) (σ y)
       grind)
    | exact superpose eq427 eq16
    | (have j1 := eq427 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq427 X0 X1
       grind)
    | exact superpose eq427 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq427 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq427 X0 X1
       grind)
    | exact resolve eq13 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq473 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq470 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq477 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq473 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq473 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq473 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq479 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq458
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq458
    | exact resolve eq458 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458
  have eq504 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq477 X0 (τ X1)
       grind)
    | exact superpose eq477 eq17
    | (have j1 := eq477 X0 (τ X1)
       grind)
    | exact resolve eq17 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq510 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq477 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq938 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq370 X0 X1
       grind)
    | exact superpose eq370 eq18
    | (have j1 := eq370 X0 X1
       grind)
    | exact resolve eq18 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq1131 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq504 (τ X0) X1
       grind)
    | exact superpose eq504 eq18
    | (have j1 := eq504 (τ X0) X1
       grind)
    | exact resolve eq18 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq504
  have eq1140 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1131 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1131
    | (have j0 := eq1131 X0 X1
       grind)
    | exact resolve eq1131 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131
  have eq1155 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1140 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1140
    | (have j0 := eq1140 X0 X1
       grind)
    | exact resolve eq1140 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq1158 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1155 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1155
    | (have j0 := eq1155 X0 X1
       grind)
    | exact resolve eq1155 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155
  have eq1218 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1158 X0 X1
       have i₂ := eq477 X0 X1
       grind)
    | exact superpose eq477 eq1158
    | (have j0 := eq1158 X0 X1
       have j1 := eq477 X0 X1
       grind)
    | exact resolve eq1158 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477 eq1158
  have eq1285 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1218 X0 X1
       have j1 := eq510 X1 X0
       grind)
    | (have r₁ := eq1218 X1 X0
       have r₂ := eq510 X0 X1
       grind)
    | exact resolve eq1218 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510 eq1218
  have eq1326 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq1285 (σ X0) X1
       grind)
    | exact superpose eq1285 eq22
    | (have j1 := eq1285 (σ X0) X1
       grind)
    | exact resolve eq22 eq1285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1285
  have eq1364 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1326 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1326
    | (have j0 := eq1326 X0 X1
       grind)
    | exact resolve eq1326 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326
  have eq1385 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1364 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1364
    | (have j0 := eq1364 X0 X1
       grind)
    | exact resolve eq1364 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1364
  have eq2014 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1385 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1385
    | exact resolve eq1385 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1385
  have eq2092 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2014 y x
       grind)
    | exact superpose eq2014 eq16
    | (have j1 := eq2014 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq2014 y x
       grind)
    | exact resolve eq16 eq2014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2014
  have eq2123 : x = (k y x) := by grind
  clear eq2092
  have eq3202 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq938 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq938
    | exact resolve eq938 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938
  have eq3284 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3202 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3202
    | (have j0 := eq3202 X0 X1
       grind)
    | exact resolve eq3202 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3202
  have eq3314 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3284 x y
       have i₂ := eq2123
       grind)
    | exact superpose eq2123 eq3284
    | (have j0 := eq3284 x y
       grind)
    | exact resolve eq3284 eq2123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3284
  have eq3379 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq479
       have i₂ := eq3314
       grind)
    | exact superpose eq3314 eq479
    | (have r₁ := eq479
       have r₂ := eq3314
       grind)
    | exact resolve eq479 eq3314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3388 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3379
  have eq3390 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq3388
       have r₂ := eq479
       grind)
    | exact resolve eq3388 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479 eq3388
  have eq3391 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3390
       have i₂ := eq2123
       grind)
    | exact superpose eq2123 eq3390
    | exact resolve eq3390 eq2123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2123 eq3390
  have eq3394 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3391
       grind)
    | exact superpose eq3391 eq16
    | exact resolve eq16 eq3391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3391
  have eq3414 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3394
       have i₂ := eq3314
       grind)
    | exact superpose eq3314 eq3394
    | (have r₁ := eq3394
       have r₂ := eq3314
       grind)
    | exact resolve eq3394 eq3314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3314
  have eq3421 : (σ (M.op x y)) = (σ x) := by grind
  clear eq3414
  have eq3424 : False := by grind
  exact eq3424

/-- `Equation4312`: `x ◇ (x ◇ y) = z ◇ (w ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_pxx_pxx_pxy_Equation4312 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4312 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4312.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X3 X3)) := by
    intro X0 X1 X2 X3
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 (k X0 X1)
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
  clear eq36
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
  have eq175 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0 X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq175 x x
       have i₂ := eq176 x x
       grind)
    | exact superpose eq176 eq175
    | exact resolve eq175 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq189 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq176 X0 (M.op x x)
       have i₂ := eq176 (M.op x x) x
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2 (M.op x x)
       have i₂ := eq176 (M.op x x) x
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq443 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq359 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq359
    | exact resolve eq359 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq874 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op X0 X0) = (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq189 eq28
    | (have j0 := eq28 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq28 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq189 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq28 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq875 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have j0 := eq874 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq920 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
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
  have eq925 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq1010 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) ∨ (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 ∨ (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq875 X0
       grind)
    | exact superpose eq875 eq11
    | exact resolve eq11 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1022 : ∀ X0 X1 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) ≠ X1 ∨ (k X0 X1) = (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq875 X0
       grind)
    | exact superpose eq875 eq13
    | (have r₁ := eq13 X0 (k X0 (M.op (σ x) (M.op (σ x) (σ y))))
       have r₂ := eq875 X0
       grind)
    | exact resolve eq13 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1038 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) ∨ (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have j0 := eq1010 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010
  have eq1051 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1038 X0
       have j1 := eq1022 X0 X0
       grind)
    | (have r₁ := eq1038 X0
       have r₂ := eq1022 X0 (k X0 X0)
       grind)
    | (have r₁ := eq1038 (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq1022 (M.op (σ x) (M.op (σ x) (σ y))) (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y))))
       grind)
    | (have r₁ := eq1038 x
       have r₂ := eq1022 x x
       grind)
    | exact resolve eq1038 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022 eq1038
  have eq1061 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq875 (M.op sF2 sF4)
       have i₂ := eq1051 (M.op sF2 sF4)
       grind)
    | exact superpose eq1051 eq875
    | exact resolve eq875 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1073 : ∀ X0 : G, (k (σ X0) (M.op (σ x) (M.op (σ x) (σ y)))) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq1051 (σ X0)
       grind)
    | exact superpose eq1051 eq10
    | exact resolve eq10 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1075 : ∀ X0 : G, (k (τ X0) (M.op (σ x) (M.op (σ x) (σ y)))) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq443 X0 X0
       have i₂ := eq1051 (τ X0)
       grind)
    | exact superpose eq1051 eq443
    | exact resolve eq443 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051
  have eq1139 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X1 X0
       have i₂ := eq1061 X0
       grind)
    | exact superpose eq1061 eq176
    | exact resolve eq176 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1177 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1139 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1139
    | exact resolve eq1139 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1178 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1139 (τ X0) X1
       have i₂ := eq443 X0 X0
       grind)
    | exact superpose eq443 eq1139
    | exact resolve eq1139 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1191 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1061 (k X0 X0)
       have i₂ := eq1139 X0 (k X0 X0)
       grind)
    | exact superpose eq1139 eq1061
    | exact resolve eq1061 eq1139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1392 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (σ (σ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1177 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1177
    | exact resolve eq1177 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1413 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ (k X0 X0)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq875 (σ (k X0 X0))
       have i₂ := eq1177 X0 (σ (k X0 X0))
       grind)
    | exact superpose eq1177 eq875
    | exact resolve eq875 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1452 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (τ (τ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1178 (τ X0) X1
       have i₂ := eq443 X0 X0
       grind)
    | exact superpose eq443 eq1178
    | exact resolve eq1178 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1475 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (τ (k X0 X0)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq875 (τ (k X0 X0))
       have i₂ := eq1178 X0 (τ (k X0 X0))
       grind)
    | exact superpose eq1178 eq875
    | exact resolve eq875 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq3036 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (σ (σ (σ (k X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1392 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1392
    | exact resolve eq1392 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3062 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ (σ (k X0 X0))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq875 (σ (σ (k X0 X0)))
       have i₂ := eq1392 X0 (σ (σ (k X0 X0)))
       grind)
    | exact superpose eq1392 eq875
    | exact resolve eq875 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392
  have eq3148 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (τ (τ (k X0 X0))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq875 (τ (τ (k X0 X0)))
       have i₂ := eq1452 X0 (τ (τ (k X0 X0)))
       grind)
    | exact superpose eq1452 eq875
    | exact resolve eq875 eq1452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452
  have eq4094 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ (σ (σ (k X0 X0)))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq875 (σ (σ (σ (k X0 X0))))
       have i₂ := eq3036 X0 (σ (σ (σ (k X0 X0))))
       grind)
    | exact superpose eq3036 eq875
    | exact resolve eq875 eq3036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875 eq3036
  have eq5366 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq920
       grind)
    | exact superpose eq920 eq41
    | exact resolve eq41 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq5367 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5366
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5366
    | exact resolve eq5366 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5366
  have eq5369 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq5367
    | exact resolve eq5367 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5367
  have eq5371 : y = (k y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5369
       have i₂ := eq1061 y
       grind)
    | exact superpose eq1061 eq5369
    | exact resolve eq5369 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5369
  have eq5373 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq5371
       have i₂ := eq1061 x
       grind)
    | exact superpose eq1061 eq5371
    | exact resolve eq5371 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5371
  have eq31370 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (k x x) := by
    first
    | exact superpose eq5373 eq925
    | exact resolve eq925 eq5373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925 eq5373
  have eq31377 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (k x x) := by
    first
    | (have r₁ := eq31370
       have r₂ := eq27
       grind)
    | exact resolve eq31370 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31370
  have eq31383 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq31377
       have i₂ := eq1061 sF3
       grind)
    | exact superpose eq1061 eq31377
    | exact resolve eq31377 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31377
  have eq31385 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (k y y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq31383
       have i₂ := eq1061 sF2
       grind)
    | exact superpose eq1061 eq31383
    | exact resolve eq31383 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31383
  have eq31393 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (k y y) ∨ y = (k x x) := by
    first
    | exact superpose eq31385 eq153
    | exact resolve eq153 eq31385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq31385
  have eq31443 : y = (k y y) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (k y y) ∨ y = (k x x) := by
    first
    | exact superpose eq32 eq31393
    | exact resolve eq31393 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31393
  have eq31444 : (σ y) = (k (σ x) (σ x)) ∨ y = (k y y) ∨ y = (k x x) := by grind
  clear eq31443
  have eq31465 : (τ (σ y)) = (k x x) ∨ y = (k y y) ∨ y = (k x x) := by
    first
    | exact superpose eq31444 eq98
    | exact resolve eq98 eq31444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31444
  have eq31515 : y = (k x x) ∨ y = (k y y) ∨ y = (k x x) := by
    first
    | exact superpose eq32 eq31465
    | exact resolve eq31465 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31465
  have eq31516 : y = (k y y) ∨ y = (k x x) := by grind
  clear eq31515
  have eq31540 : (σ y) = (k (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq31516
       grind)
    | exact superpose eq31516 eq41
    | exact resolve eq41 eq31516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31552 : (k y y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq1191 y
       have i₂ := eq31516
       grind)
    | exact superpose eq31516 eq1191
    | exact resolve eq1191 eq31516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31554 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq1413 y
       have i₂ := eq31516
       grind)
    | exact superpose eq31516 eq1413
    | exact resolve eq1413 eq31516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413
  have eq31582 : (σ (k y y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | exact superpose eq1073 eq31554
    | exact resolve eq31554 eq1073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31554
  have eq31584 : y = (k x x) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq31516 eq31552
    | exact resolve eq31552 eq31516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31552
  have eq31589 : (σ y) = (k (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq31540
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31540
    | exact resolve eq31540 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31540
  have eq31598 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq31582
       have i₂ := eq41 y
       grind)
    | exact superpose eq41 eq31582
    | exact resolve eq31582 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31582
  have eq31605 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq31598
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31598
    | exact resolve eq31598 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31598
  have eq31610 : y = (k (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | exact superpose eq31584 eq31605
    | exact resolve eq31605 eq31584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31605
  have eq31615 : y = (k x x) ∨ y = (σ y) := by
    first
    | exact superpose eq31589 eq31610
    | exact resolve eq31610 eq31589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31589 eq31610
  have eq31628 : (σ y) = (k (σ x) (σ x)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq31615
       grind)
    | exact superpose eq31615 eq40
    | exact resolve eq40 eq31615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31635 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 y) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1139 x X0
       have i₂ := eq31615
       grind)
    | exact superpose eq31615 eq1139
    | exact resolve eq1139 eq31615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31638 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (σ y)) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1177 x X0
       have i₂ := eq31615
       grind)
    | exact superpose eq31615 eq1177
    | exact resolve eq1177 eq31615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177
  have eq31640 : (k y y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (σ y) := by
    first
    | (have i₁ := eq1191 x
       have i₂ := eq31615
       grind)
    | exact superpose eq31615 eq1191
    | exact resolve eq1191 eq31615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31647 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (σ y) := by
    first
    | (have i₁ := eq3062 x
       have i₂ := eq31615
       grind)
    | exact superpose eq31615 eq3062
    | exact resolve eq3062 eq31615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3062
  have eq31651 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ (σ (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (σ y) := by
    first
    | (have i₁ := eq4094 x
       have i₂ := eq31615
       grind)
    | exact superpose eq31615 eq4094
    | exact resolve eq4094 eq31615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4094 eq31615
  have eq31659 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (k (σ (σ y)) (σ (σ y)))) ∨ y = (σ y) := by
    first
    | exact superpose eq1073 eq31651
    | exact resolve eq31651 eq1073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31651
  have eq31662 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (k (σ y) (σ y))) ∨ y = (σ y) := by
    first
    | exact superpose eq1073 eq31647
    | exact resolve eq31647 eq1073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073 eq31647
  have eq31669 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (σ y)) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq31638 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31638
    | (have j0 := eq31638 X0
       grind)
    | exact resolve eq31638 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31638
  have eq31671 : ∀ X0 : G, (k y y) = (M.op X0 y) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq31640 eq31635
    | exact resolve eq31635 eq31640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31635
  have eq31675 : (σ y) = (k (σ x) (σ x)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq31628
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31628
    | exact resolve eq31628 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31628
  have eq31681 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (σ (k (σ y) (σ y)))) ∨ y = (σ y) := by
    first
    | (have i₁ := eq31659
       have i₂ := eq10 (σ y) (σ y)
       grind)
    | exact superpose eq10 eq31659
    | exact resolve eq31659 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31659
  have eq31684 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (σ (k y y))) ∨ y = (σ y) := by
    first
    | (have i₁ := eq31662
       have i₂ := eq10 y y
       grind)
    | exact superpose eq10 eq31662
    | exact resolve eq31662 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31662
  have eq31690 : ∀ X0 : G, (k y y) = (M.op X0 (σ y)) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq31640 eq31669
    | exact resolve eq31669 eq31640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31669
  have eq31693 : (σ y) = (k (σ x) (σ x)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq31675
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31675
    | exact resolve eq31675 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31675
  have eq31696 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (σ (σ (k y y)))) ∨ y = (σ y) := by
    first
    | (have i₁ := eq31681
       have i₂ := eq10 y y
       grind)
    | exact superpose eq10 eq31681
    | exact resolve eq31681 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31681
  have eq31698 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (k (σ y) (σ y))) ∨ y = (σ y) := by
    first
    | (have i₁ := eq31684
       have i₂ := eq41 y
       grind)
    | exact superpose eq41 eq31684
    | exact resolve eq31684 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31684
  have eq31703 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (σ (k (σ y) (σ y)))) ∨ y = (σ y) := by
    first
    | (have i₁ := eq31696
       have i₂ := eq41 y
       grind)
    | exact superpose eq41 eq31696
    | exact resolve eq31696 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31696
  have eq31705 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (k (σ y) (σ y))) ∨ y = (σ y) := by
    first
    | (have i₁ := eq31698
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31698
    | exact resolve eq31698 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31698
  have eq31707 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (σ (k (σ y) (σ y)))) ∨ y = (σ y) := by
    first
    | (have i₁ := eq31703
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31703
    | exact resolve eq31703 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31703
  have eq31708 : (k y y) = (σ (k (σ y) (σ y))) ∨ y = (σ y) := by
    first
    | exact superpose eq31640 eq31705
    | exact resolve eq31705 eq31640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31705
  have eq31710 : (k y y) = (σ (σ (k (σ y) (σ y)))) ∨ y = (σ y) := by
    first
    | exact superpose eq31640 eq31707
    | exact resolve eq31707 eq31640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31707
  have eq31711 : (k y y) = (σ (k y y)) ∨ y = (σ y) := by
    first
    | exact superpose eq31708 eq31710
    | exact resolve eq31710 eq31708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31708 eq31710
  have eq31712 : (k y y) = (k (σ y) (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq31711
       have i₂ := eq41 y
       grind)
    | exact superpose eq41 eq31711
    | exact resolve eq31711 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31711
  have eq31713 : (k y y) = (k (σ y) (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq31712
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31712
    | exact resolve eq31712 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31712
  have eq32269 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq31584
       grind)
    | exact superpose eq31584 eq40
    | exact resolve eq40 eq31584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq31584
  have eq32323 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq32269
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32269
    | exact resolve eq32269 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq32269
  have eq32338 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq32323
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq32323
    | exact resolve eq32323 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32323
  have eq32349 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq31693 eq32338
    | exact resolve eq32338 eq31693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31693 eq32338
  have eq32689 : (τ (σ y)) = (k x x) ∨ (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq32349 eq98
    | exact resolve eq98 eq32349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq32349
  have eq32752 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | exact superpose eq32 eq32689
    | exact resolve eq32689 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq32689
  have eq33696 : (M.op x y) = (k y y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq31671 x
       grind)
    | exact superpose eq31671 eq18
    | (have j1 := eq31671 x
       grind)
    | exact resolve eq18 eq31671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31671
  have eq33738 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq33696
       grind)
    | exact superpose eq33696 eq41
    | exact resolve eq41 eq33696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33754 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (τ (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (σ y) := by
    first
    | (have i₁ := eq1475 y
       have i₂ := eq33696
       grind)
    | exact superpose eq33696 eq1475
    | exact resolve eq1475 eq33696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475
  have eq33759 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (τ (τ (M.op x y))) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (σ y) := by
    first
    | (have i₁ := eq3148 y
       have i₂ := eq33696
       grind)
    | exact superpose eq33696 eq3148
    | exact resolve eq3148 eq33696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3148
  have eq33773 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ (k (τ (M.op x y)) (τ (M.op x y)))) ∨ y = (σ y) := by
    first
    | exact superpose eq1075 eq33759
    | exact resolve eq33759 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33759
  have eq33778 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ (k (M.op x y) (M.op x y))) ∨ y = (σ y) := by
    first
    | exact superpose eq1075 eq33754
    | exact resolve eq33754 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075 eq33754
  have eq33789 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq33738
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq33738
    | exact resolve eq33738 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33738
  have eq33799 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ (τ (k (M.op x y) (M.op x y)))) ∨ y = (σ y) := by
    first
    | (have i₁ := eq33773
       have i₂ := eq443 sF0 sF0
       grind)
    | exact superpose eq443 eq33773
    | exact resolve eq33773 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443 eq33773
  have eq33804 : (k y y) = (τ (k (M.op x y) (M.op x y))) ∨ y = (σ y) := by
    first
    | exact superpose eq31640 eq33778
    | exact resolve eq33778 eq31640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33778
  have eq33814 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq33789
    | exact resolve eq33789 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33789
  have eq33820 : (k y y) = (τ (τ (k (M.op x y) (M.op x y)))) ∨ y = (σ y) := by
    first
    | exact superpose eq31640 eq33799
    | exact resolve eq33799 eq31640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31640 eq33799
  have eq33824 : (k (σ y) (σ y)) = (τ (k (M.op x y) (M.op x y))) ∨ y = (σ y) := by
    first
    | exact superpose eq31713 eq33804
    | exact resolve eq33804 eq31713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33804
  have eq33833 : (k (σ y) (σ y)) = (τ (τ (k (M.op x y) (M.op x y)))) ∨ y = (σ y) := by
    first
    | exact superpose eq31713 eq33820
    | exact resolve eq33820 eq31713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31713 eq33820
  have eq33836 : (σ (M.op x y)) = (τ (k (M.op x y) (M.op x y))) ∨ y = (σ y) := by
    first
    | exact superpose eq33814 eq33824
    | exact resolve eq33824 eq33814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33824
  have eq33843 : (σ (M.op x y)) = (τ (τ (k (M.op x y) (M.op x y)))) ∨ y = (σ y) := by
    first
    | exact superpose eq33814 eq33833
    | exact resolve eq33833 eq33814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33814 eq33833
  have eq33848 : (σ (M.op x y)) = (τ (σ (M.op x y))) ∨ y = (σ y) := by
    first
    | exact superpose eq33836 eq33843
    | exact resolve eq33843 eq33836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33836 eq33843
  have eq33853 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq29 eq33848
    | exact resolve eq33848 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq33848
  have eq35328 : (M.op (σ x) (σ y)) = (k y y) ∨ y = (σ y) := by
    first
    | exact superpose eq31690 eq26
    | (have j1 := eq31690 (σ x)
       grind)
    | exact resolve eq26 eq31690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31690
  have eq35331 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq33696 eq35328
    | exact resolve eq35328 eq33696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33696 eq35328
  have eq35368 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq35331 eq27
    | exact resolve eq27 eq35331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35331
  have eq35530 : y = (σ y) := by
    first
    | (have r₁ := eq35368
       have r₂ := eq33853
       grind)
    | exact resolve eq35368 eq33853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33853 eq35368
  have eq35575 : (M.op x y) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq35530
       grind)
    | exact superpose eq35530 eq18
    | exact resolve eq18 eq35530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq35576 : (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq24
       have i₂ := eq35530
       grind)
    | exact superpose eq35530 eq24
    | exact resolve eq24 eq35530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq35578 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq35530
       grind)
    | exact superpose eq35530 eq41
    | exact resolve eq41 eq35530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq35602 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (k x x) := by
    first
    | (have i₁ := eq31516
       have i₂ := eq35530
       grind)
    | exact superpose eq35530 eq31516
    | exact resolve eq31516 eq35530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31516
  have eq39152 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq32752 eq197
    | exact resolve eq197 eq32752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32752
  have eq39153 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq26 eq39152
    | (have j0 := eq39152 X0
       grind)
    | exact resolve eq39152 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39152
  have eq39228 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (k x x) := by
    intro X0
    first
    | (have i₁ := eq39153 X0
       have i₂ := eq35530
       grind)
    | exact superpose eq35530 eq39153
    | (have j0 := eq39153 X0
       grind)
    | exact resolve eq39153 eq35530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35530 eq39153
  have eq39436 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k x x) := by
    first
    | exact superpose eq39228 eq1061
    | exact resolve eq1061 eq39228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061
  have eq39448 : (σ y) = (k x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39228 eq35575
    | exact resolve eq35575 eq39228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39228
  have eq39461 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k x x) := by
    first
    | exact superpose eq35602 eq39436
    | exact resolve eq39436 eq35602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35602 eq39436
  have eq39486 : (σ y) = (k x x) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq39448 eq39461
    | exact resolve eq39461 eq39448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39448 eq39461
  have eq39551 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1139 x X0
       have i₂ := eq39486
       grind)
    | exact superpose eq39486 eq1139
    | exact resolve eq1139 eq39486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1139
  have eq39556 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq1191 x
       have i₂ := eq39486
       grind)
    | exact superpose eq39486 eq1191
    | exact resolve eq1191 eq39486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191 eq39486
  have eq39596 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq39556 eq39551
    | exact resolve eq39551 eq39556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39551 eq39556
  have eq44285 : (M.op x y) = (k (σ y) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq39596 eq35575
    | exact resolve eq35575 eq39596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44286 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq39596 eq26
    | (have j1 := eq39596 (σ x)
       grind)
    | exact resolve eq26 eq39596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39596
  have eq44345 : (σ (M.op x y)) = (k (σ (σ y)) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq44285 eq35578
    | exact resolve eq35578 eq44285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35578
  have eq44410 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq35576 eq44345
    | exact resolve eq44345 eq35576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44345
  have eq44445 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq20 eq44410
    | exact resolve eq44410 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44410
  have eq44467 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq44285 eq44445
    | exact resolve eq44445 eq44285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44445
  have eq44576 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq44467 eq35576
    | exact resolve eq35576 eq44467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35576 eq44467
  have eq44608 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq44576
    | exact resolve eq44576 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq44576
  have eq44609 : (M.op x y) = (σ (M.op x y)) := by grind
  clear eq44608
  have eq46150 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq44286 eq44285
    | exact resolve eq44285 eq44286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44285 eq44286
  have eq46191 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by grind
  clear eq46150
  have eq46365 : (M.op x y) ≠ (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq46191 eq27
    | exact resolve eq27 eq46191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46191
  have eq46533 : (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq46365
       have r₂ := eq44609
       grind)
    | exact resolve eq46365 eq44609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46365
  have eq46575 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq46533 eq26
    | exact resolve eq26 eq46533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq46647 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq46533 eq35575
    | exact resolve eq35575 eq46533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35575 eq46533
  have eq46952 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq46647 eq184
    | exact resolve eq184 eq46647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq46647
  have eq46993 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq46952 eq189
    | exact resolve eq189 eq46952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq47085 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (σ x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq46952 eq197
    | exact resolve eq197 eq46952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq46952
  have eq47090 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq46575 eq47085
    | exact resolve eq47085 eq46575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46575 eq47085
  have eq47138 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46993 eq47090
    | exact resolve eq47090 eq46993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46993 eq47090
  have eq47204 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq47138 eq27
    | exact resolve eq27 eq47138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq47138
  have eq47371 : False := by grind
  exact eq47371
