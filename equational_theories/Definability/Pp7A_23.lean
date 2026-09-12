import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pxx_pyx_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
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
  have eq175 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
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
  have eq176 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
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
  have eq180 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq175 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq175 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq175 eq175
    | exact resolve eq175 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq559 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X2 ∨ (M.op X2 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq539 X0 X1
       grind)
    | (have i₁ := eq13 X2 X1
       have i₂ := eq539 X1 X0
       grind)
    | exact superpose eq539 eq13
    | (have j0 := eq13 X2 X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X1
       have r₂ := eq539 X0 X1
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X0
       have r₂ := eq539 X0 X1
       grind)
    | exact resolve eq13 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq570 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq180 X1
       have i₂ := eq539 X0 X1
       grind)
    | (have i₁ := eq180 X0
       have i₂ := eq539 X0 X1
       grind)
    | exact superpose eq539 eq180
    | exact resolve eq180 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : ∀ X0 X1 : G, (M.op (k (M.op X0 X0) X0) (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq180 X0
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : x = (M.op (k (M.op y y) y) (M.op x y)) := by
    first
    | (have i₁ := eq176 y
       have i₂ := eq180 y
       grind)
    | exact superpose eq180 eq176
    | exact resolve eq176 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq180
  have eq579 : ∀ X0 : G, x = (M.op (k (M.op X0 X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq573
       have i₂ := eq539 X0 y
       grind)
    | (have i₁ := eq573
       have i₂ := eq539 y X0
       grind)
    | exact superpose eq539 eq573
    | exact resolve eq573 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq675 : ∀ X0 X1 X2 : G, (M.op (k (M.op X0 X0) X1) (M.op X2 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq572 X1 X2
       have i₂ := eq539 X0 X1
       grind)
    | (have i₁ := eq572 X1 X2
       have i₂ := eq539 X1 X0
       grind)
    | exact superpose eq539 eq572
    | exact resolve eq572 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1214 : (M.op x x) = (M.op y x) ∨ (M.op x y) = (k y x) ∨ y = (M.op x x) := by
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
  have eq1215 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq1316 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1320 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1316 X0
       have j1 := eq559 X0 X0 X0
       grind)
    | (have r₁ := eq1316 x
       have r₂ := eq559 x x x
       grind)
    | (have r₁ := eq1316 (M.op X0 X0)
       have r₂ := eq559 X0 x (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | (have r₁ := eq1316 X0
       have r₂ := eq559 X0 x (k X0 X0)
       grind)
    | exact resolve eq1316 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559 eq1316
  have eq1463 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq539 X0 X1
       have i₂ := eq1320 X0
       grind)
    | exact superpose eq1320 eq539
    | exact resolve eq539 eq1320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq1473 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (k (k X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq570 X0 X1
       have i₂ := eq1320 X0
       grind)
    | exact superpose eq1320 eq570
    | exact resolve eq570 eq1320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq1475 : ∀ X0 : G, x = (M.op (k (k X0 X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq579 X0
       have i₂ := eq1320 X0
       grind)
    | exact superpose eq1320 eq579
    | exact resolve eq579 eq1320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq1477 : ∀ X0 X1 X2 : G, (M.op (k (k X0 X0) X1) (M.op X2 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq675 X0 X1 X2
       have i₂ := eq1320 X0
       grind)
    | exact superpose eq1320 eq675
    | exact resolve eq675 eq1320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq1577 : ∀ X0 X1 : G, (k X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1320 X0
       have i₂ := eq1463 X1 X0
       grind)
    | exact superpose eq1463 eq1320
    | exact resolve eq1320 eq1463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1600 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq1463 (σ X1) X0
       grind)
    | exact superpose eq1463 eq10
    | exact resolve eq10 eq1463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1463
  have eq1815 : ∀ X0 X1 : G, (M.op (k (σ (k X0 X0)) X1) (σ (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq572 X0 X0
       have i₂ := eq1600 X0 X1
       grind)
    | exact superpose eq1600 eq572
    | exact resolve eq572 eq1600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq1600
  have eq5146 : ∀ X0 : G, y = (M.op (M.op (M.op X0 X0) x) (M.op x x)) ∨ (M.op x y) = (k y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 x
       have i₂ := eq1214
       grind)
    | exact superpose eq1214 eq16
    | exact resolve eq16 eq1214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq5149 : x = y ∨ (M.op x y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5146 x
       have i₂ := eq16 x x x
       grind)
    | exact superpose eq16 eq5146
    | exact resolve eq5146 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5146
  have eq5156 : (M.op x y) = (k y x) ∨ x = y ∨ y = (k x x) := by
    first
    | (have i₁ := eq5149
       have i₂ := eq1320 x
       grind)
    | exact superpose eq1320 eq5149
    | exact resolve eq5149 eq1320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5149
  have eq12067 : ∀ X0 : G, (σ y) = (M.op (k (k X0 X0) (σ x)) (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq1215 eq1477
    | exact resolve eq1477 eq1215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215
  have eq12070 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq12067 x
       have i₂ := eq1477 x sF2 sF2
       grind)
    | exact superpose eq1477 eq12067
    | exact resolve eq12067 eq1477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477 eq12067
  have eq12078 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq12070
       have i₂ := eq1320 sF2
       grind)
    | exact superpose eq1320 eq12070
    | exact resolve eq12070 eq1320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12070
  have eq45320 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (k x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq5156
       grind)
    | exact superpose eq5156 eq39
    | exact resolve eq39 eq5156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5156
  have eq45321 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (k x x) := by
    first
    | (have i₁ := eq45320
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq45320
    | exact resolve eq45320 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45320
  have eq45323 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (k x x) := by
    first
    | exact superpose eq20 eq45321
    | exact resolve eq45321 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45321
  have eq94547 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (k x x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq12078 eq45323
    | exact resolve eq45323 eq12078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12078 eq45323
  have eq94553 : (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq94547
       have r₂ := eq27
       grind)
    | exact resolve eq94547 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94547
  have eq94563 : (τ (σ y)) = (k x x) ∨ y = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq94553 eq97
    | exact resolve eq97 eq94553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq94553
  have eq94948 : y = (k x x) ∨ y = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq31 eq94563
    | exact resolve eq94563 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94563
  have eq94949 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq94948
  have eq95057 : x = (M.op (k y y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1475 x
       have i₂ := eq94949
       grind)
    | exact superpose eq94949 eq1475
    | exact resolve eq1475 eq94949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475
  have eq95076 : ∀ X0 : G, y = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1577 x X0
       have i₂ := eq94949
       grind)
    | exact superpose eq94949 eq1577
    | exact resolve eq1577 eq94949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1577
  have eq95092 : ∀ X0 : G, (M.op (k (σ y) X0) (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1815 x x
       have i₂ := eq94949
       grind)
    | exact superpose eq94949 eq1815
    | exact resolve eq1815 eq94949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1815 eq94949
  have eq95410 : ∀ X0 : G, (M.op (k (σ y) X0) (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq95092 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq95092
    | (have j0 := eq95092 X0
       grind)
    | exact resolve eq95092 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95092
  have eq95433 : x = (k (k y y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq95057
       have i₂ := eq1473 y sF0
       grind)
    | exact superpose eq1473 eq95057
    | exact resolve eq95057 eq1473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473 eq95057
  have eq95531 : x = (k y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq95076 eq95433
    | exact resolve eq95433 eq95076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95076 eq95433
  have eq100992 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq95531 eq41
    | exact resolve eq41 eq95531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq95531
  have eq100993 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq100992
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq100992
    | exact resolve eq100992 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100992
  have eq100998 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq100993
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq100993
    | exact resolve eq100993 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100993
  have eq107252 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq100998 eq95410
    | exact resolve eq95410 eq100998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95410 eq100998
  have eq107298 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq107252
  have eq107335 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq107298
    | exact resolve eq107298 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107298
  have eq107376 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq107335
       have r₂ := eq27
       grind)
    | exact resolve eq107335 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107335
  have eq107404 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq107376 eq31
    | exact resolve eq31 eq107376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq107376
  have eq107539 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq107404
    | exact resolve eq107404 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq107404
  have eq107540 : x = y := by grind
  clear eq107539
  have eq107589 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq107540
       grind)
    | exact superpose eq107540 eq18
    | exact resolve eq18 eq107540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq107590 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq107540
       grind)
    | exact superpose eq107540 eq24
    | exact resolve eq24 eq107540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq107540
  have eq107649 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq107590
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq107590
    | exact resolve eq107590 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107590
  have eq107650 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq107589
       have i₂ := eq1320 x
       grind)
    | exact superpose eq1320 eq107589
    | exact resolve eq107589 eq1320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107589
  have eq109067 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq107649 eq26
    | exact resolve eq26 eq107649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq107649
  have eq109195 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq109067
       have i₂ := eq1320 sF2
       grind)
    | exact superpose eq1320 eq109067
    | exact resolve eq109067 eq1320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320 eq109067
  have eq109218 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq107650
       grind)
    | exact superpose eq107650 eq39
    | exact resolve eq39 eq107650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq107650
  have eq109610 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq109218
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq109218
    | exact resolve eq109218 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq109218
  have eq109716 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq109195 eq109610
    | exact resolve eq109610 eq109195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109195 eq109610
  have eq109786 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq109716
    | exact resolve eq109716 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq109716
  have eq109822 : False := by grind
  exact eq109822

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyx_x_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq175 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
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
  have eq176 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
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
  have eq177 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (M.op (M.op X1 X1) y) = (M.op (M.op (M.op X0 X0) (M.op x y)) x) := by
    intro X0 X1
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq539 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq175 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq175 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq175 eq175
    | exact resolve eq175 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq175 X0 X2 (M.op (M.op X1 X1) (M.op X2 X2))
       have i₂ := eq16 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq539 X0 X2
       grind)
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq539 X2 X0
       grind)
    | exact superpose eq539 eq16
    | exact resolve eq16 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq568 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X2 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 (M.op X1 X1)
       have i₂ := eq539 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq16 X2 X1 (M.op X1 X1)
       have i₂ := eq539 (M.op X1 X1) X0
       grind)
    | exact superpose eq539 eq16
    | exact resolve eq16 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq570 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq180 X1
       have i₂ := eq539 X0 X1
       grind)
    | (have i₁ := eq180 X0
       have i₂ := eq539 X0 X1
       grind)
    | exact superpose eq539 eq180
    | exact resolve eq180 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq571 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq180 (M.op (M.op X1 X1) x)
       have i₂ := eq16 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq16 eq180
    | exact resolve eq180 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (k (M.op X0 X0) X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq175 X0 X0 X1
       have i₂ := eq180 X0
       grind)
    | exact superpose eq180 eq175
    | exact resolve eq175 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq576 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq571 X0 X1
       have i₂ := eq564 X0 X0 X1
       grind)
    | exact superpose eq564 eq571
    | exact resolve eq571 eq564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq646 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (k (M.op X0 X0) X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq572 X1 X2
       have i₂ := eq539 X0 X1
       grind)
    | (have i₁ := eq572 X1 X2
       have i₂ := eq539 X1 X0
       grind)
    | exact superpose eq539 eq572
    | exact resolve eq572 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq651 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X1 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq572 X1 (k (M.op X1 X1) X1)
       have i₂ := eq539 X0 (k (M.op X1 X1) X1)
       grind)
    | (have i₁ := eq572 X1 (k (M.op X1 X1) X1)
       have i₂ := eq539 (k (M.op X1 X1) X1) X0
       grind)
    | exact superpose eq539 eq572
    | exact resolve eq572 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq670 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq576 X1 (M.op X2 X2)
       have i₂ := eq540 X0 X1 X2
       grind)
    | (have i₁ := eq576 X0 (M.op X0 X0)
       have i₂ := eq540 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq540 eq576
    | exact resolve eq576 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq671 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2))) = (k (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq576 X1 (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2)))
       have i₂ := eq175 (M.op X1 X1) X2 X0
       grind)
    | exact superpose eq175 eq576
    | exact resolve eq576 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq676 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq576 X1 (M.op X1 X1)
       have i₂ := eq539 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq576 X1 (M.op X1 X1)
       have i₂ := eq539 (M.op X1 X1) X0
       grind)
    | exact superpose eq539 eq576
    | exact resolve eq576 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq680 : ∀ X0 X1 X2 : G, (k (M.op X1 X1) X0) = (M.op X0 (k (M.op X2 X2) (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq671 X0 X1 X2
       have i₂ := eq570 X2 (M.op X1 X1)
       grind)
    | exact superpose eq570 eq671
    | exact resolve eq671 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq685 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (k (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq680 X0 X1 X2
       have i₂ := eq676 X1 X2
       grind)
    | exact superpose eq676 eq680
    | exact resolve eq680 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq689 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3) (M.op X4 X4)) = X3 := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq564 X4 x X3
       have i₂ := eq540 x X0 X1
       grind)
    | (have i₁ := eq564 X0 (M.op x x) x
       have i₂ := eq540 X0 x x
       grind)
    | exact superpose eq540 eq564
    | exact resolve eq564 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq721 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X0) = (M.op (M.op X2 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq175 (M.op X1 X1) X1 (M.op (M.op X2 X2) X0)
       have i₂ := eq564 (M.op X1 X1) X2 X0
       grind)
    | exact superpose eq564 eq175
    | exact resolve eq175 eq564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq748 : ∀ X0 X1 X3 X4 : G, (k (M.op X4 X4) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3)) = X3 := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq689 X0 X1 X3 X4
       have i₂ := eq570 X4 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3)
       grind)
    | exact superpose eq570 eq689
    | exact resolve eq689 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq751 : ∀ X0 X1 X3 X4 : G, (k (M.op X4 X4) (M.op (k (M.op X1 X1) (M.op X0 X0)) X3)) = X3 := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq748 X0 X1 X3 X4
       have i₂ := eq570 X1 (M.op X0 X0)
       grind)
    | exact superpose eq570 eq748
    | exact resolve eq748 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq752 : ∀ X1 X3 X4 : G, (k (M.op X4 X4) (M.op (M.op X1 X1) X3)) = X3 := by
    intro X1 X3 X4
    first
    | (have i₁ := eq751 x X1 X3 X4
       have i₂ := eq676 x X1
       grind)
    | exact superpose eq676 eq751
    | exact resolve eq751 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq925 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (k (M.op X0 X0) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq568 X1 X0 X0
       have i₂ := eq180 X0
       grind)
    | exact superpose eq180 eq568
    | exact resolve eq568 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1001 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (k (M.op X0 X0) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq568 X2 X0 X1
       have i₂ := eq570 X0 X1
       grind)
    | exact superpose eq570 eq568
    | exact resolve eq568 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568 eq570
  have eq1376 : ∀ X0 X1 X2 : G, (k (M.op X0 X0) X1) = (k (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq646 X2 X1 (k (M.op X2 X2) X1)
       have i₂ := eq685 X1 X0 (k (M.op X2 X2) X1)
       grind)
    | exact superpose eq685 eq646
    | exact resolve eq646 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646 eq685
  have eq1502 : x ≠ (M.op x y) ∨ x = (M.op y y) ∨ x = (k x y) := by
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
  have eq1503 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1534 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X1
       have i₂ := eq539 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq539 X0 X1
       grind)
    | exact superpose eq539 eq11
    | (have j0 := eq11 (k X1 X1) X0
       grind)
    | exact resolve eq11 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1541 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq1542 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1602 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1603 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1604 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1603 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1603
  have eq1636 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1534 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1534
  have eq2805 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq539 X2 X1
       have i₂ := eq1636 X2 X0
       grind)
    | exact superpose eq1636 eq539
    | (have j1 := eq1636 X1 X0
       grind)
    | exact resolve eq539 eq1636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2882 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1636 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1636
  have eq3132 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1541
       grind)
    | exact superpose eq1541 eq40
    | exact resolve eq40 eq1541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3133 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3132
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3132
    | exact resolve eq3132 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3132
  have eq3135 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq3133
    | exact resolve eq3133 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3133
  have eq3401 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3135 eq1542
    | exact resolve eq1542 eq3135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3135
  have eq3408 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq3401
       have r₂ := eq27
       grind)
    | exact resolve eq3401 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3401
  have eq3427 : ∀ X0 : G, (σ x) = (M.op X0 X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq3408 eq539
    | exact resolve eq539 eq3408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3442 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ x) (M.op X1 X1)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq3408 eq670
    | exact resolve eq670 eq3408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq3444 : ∀ X0 : G, (σ x) = (k (σ x) (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq3408 eq676
    | exact resolve eq676 eq3408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3408
  have eq3485 : (σ x) = (k (σ x) (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2805 eq3444
    | (have j1 := eq2805 x x y
       grind)
    | exact resolve eq3444 eq2805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3444
  have eq3487 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq2805 eq3442
    | (have j1 := eq2805 (k (σ x) (k x x)) x X0
       grind)
    | exact resolve eq3442 eq2805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3442
  have eq3508 : (k x x) = (k (σ x) (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2805 eq3487
    | (have j1 := eq2805 x x y
       grind)
    | exact resolve eq3487 eq2805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2805 eq3487
  have eq3520 : (σ x) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3485 eq3508
    | exact resolve eq3508 eq3485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3485 eq3508
  have eq3603 : ∀ X0 : G, (σ x) = (k (σ x) (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq651 X0 (M.op X0 X0)
       have i₂ := eq3427 (M.op X0 X0)
       grind)
    | exact superpose eq3427 eq651
    | exact resolve eq651 eq3427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq3631 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3427 eq3603
    | exact resolve eq3603 eq3427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3427 eq3603
  have eq3715 : (k (σ x) (σ x)) = (σ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq3520
       grind)
    | exact superpose eq3520 eq39
    | exact resolve eq39 eq3520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3520
  have eq3719 : (k (σ x) (σ x)) = (σ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3715
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3715
    | exact resolve eq3715 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3715
  have eq3721 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ (σ x)) := by
    first
    | exact superpose eq3631 eq3719
    | exact resolve eq3719 eq3631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3719
  have eq3739 : ∀ X0 : G, x = (M.op X0 X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq539 y X0
       have i₂ := eq3721
       grind)
    | exact superpose eq3721 eq539
    | exact resolve eq539 eq3721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3757 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq676 y X0
       have i₂ := eq3721
       grind)
    | exact superpose eq3721 eq676
    | exact resolve eq676 eq3721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3770 : ∀ X0 X1 : G, (k x X1) = (k (M.op X0 X0) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq1376 X0 X1 y
       have i₂ := eq3721
       grind)
    | exact superpose eq3721 eq1376
    | exact resolve eq1376 eq3721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3721
  have eq3786 : ∀ X0 : G, (M.op X0 X0) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ (σ x)) := by
    intro X0
    first
    | exact superpose eq3770 eq3757
    | exact resolve eq3757 eq3770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3757 eq3770
  have eq3801 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ (σ x)) := by
    first
    | exact superpose eq3739 eq3786
    | exact resolve eq3786 eq3739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3786
  have eq4497 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq3801
       grind)
    | exact superpose eq3801 eq39
    | exact resolve eq39 eq3801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3801
  have eq4507 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq4497
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4497
    | exact resolve eq4497 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4497
  have eq4514 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ (σ x)) := by
    first
    | exact superpose eq4507 eq1602
    | (have j0 := eq1602 (σ x) (σ x)
       grind)
    | (have r₁ := eq1602 (σ x) (σ x)
       have r₂ := eq4507
       grind)
    | exact resolve eq1602 eq4507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4507
  have eq4515 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ (σ x)) := by grind
  clear eq4514
  have eq4516 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ (σ x)) := by grind
  clear eq4515
  have eq4577 : x = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ (σ x)) := by
    first
    | exact superpose eq4516 eq3739
    | exact resolve eq3739 eq4516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3739 eq4516
  have eq4580 : (σ x) = (σ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (σ x) := by grind
  clear eq4577
  have eq4667 : (σ x) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq4580 eq15
    | exact resolve eq15 eq4580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4580
  have eq4684 : x = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq29 eq4667
    | exact resolve eq4667 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4667
  have eq4685 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by grind
  clear eq4684
  have eq5033 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3631 eq141
    | exact resolve eq141 eq3631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3631
  have eq5041 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq5033
    | exact resolve eq5033 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5033
  have eq5044 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq2882 y x
       grind)
    | (have r₁ := eq5041
       have r₂ := eq2882 x x
       grind)
    | exact resolve eq5041 eq2882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5041
  have eq5047 : (σ x) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4685 eq5044
    | exact resolve eq5044 eq4685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5044
  have eq5066 : ∀ X0 : G, (M.op (M.op X0 X0) y) = (M.op (M.op (σ x) (M.op x y)) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq182 y X0
       have i₂ := eq5047
       grind)
    | exact superpose eq5047 eq182
    | exact resolve eq182 eq5047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5069 : ∀ X0 : G, (σ x) = (M.op X0 X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq539 y X0
       have i₂ := eq5047
       grind)
    | exact superpose eq5047 eq539
    | exact resolve eq539 eq5047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5074 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (σ x)) = X1 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq564 y X0 X1
       have i₂ := eq5047
       grind)
    | exact superpose eq5047 eq564
    | exact resolve eq564 eq5047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5081 : ∀ X0 : G, (k (σ x) (M.op (σ x) X0)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq576 y x
       have i₂ := eq5047
       grind)
    | exact superpose eq5047 eq576
    | exact resolve eq576 eq5047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq5090 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ x) X1) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq721 X1 X0 y
       have i₂ := eq5047
       grind)
    | exact superpose eq5047 eq721
    | exact resolve eq721 eq5047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5096 : ∀ X0 X1 : G, (M.op (σ x) (k (M.op X0 X0) X1)) = X1 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1001 X0 X1 y
       have i₂ := eq5047
       grind)
    | exact superpose eq5047 eq1001
    | exact resolve eq1001 eq5047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq5100 : ∀ X0 X1 : G, (k (σ x) X1) = (k (M.op X0 X0) X1) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1376 X0 X1 y
       have i₂ := eq5047
       grind)
    | exact superpose eq5047 eq1376
    | exact resolve eq1376 eq5047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5047
  have eq5121 : ∀ X1 : G, (M.op (σ x) (k (σ x) X1)) = X1 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq5100 eq5096
    | exact resolve eq5096 eq5100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5096 eq5100
  have eq5132 : ∀ X1 : G, (M.op (M.op (σ x) X1) (σ x)) = X1 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq5090 eq5074
    | exact resolve eq5074 eq5090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5074 eq5090
  have eq5136 : ∀ X0 : G, (M.op (M.op X0 X0) y) = (M.op (M.op (σ x) (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq4685 eq5066
    | exact resolve eq5066 eq4685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5066
  have eq5149 : (M.op (σ x) y) = (M.op (M.op (σ x) (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5069 eq5136
    | exact resolve eq5136 eq5069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5069 eq5136
  have eq5152 : (M.op x y) = (M.op (σ x) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5132 eq5149
    | exact resolve eq5149 eq5132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5132 eq5149
  have eq5624 : (σ y) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq5081
    | (have j0 := eq5081 (σ y)
       grind)
    | exact resolve eq5081 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5081
  have eq5689 : (τ (σ y)) = (k x (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5624 eq90
    | exact resolve eq90 eq5624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq5624
  have eq5691 : y = (k x (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq5689
    | exact resolve eq5689 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5689
  have eq5692 : y = (k (σ x) (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4685 eq5691
    | exact resolve eq5691 eq4685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4685 eq5691
  have eq5791 : (τ (M.op (σ x) (σ y))) = (M.op (σ x) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5692 eq5121
    | exact resolve eq5121 eq5692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5121 eq5692
  have eq5811 : (τ (M.op (σ x) (σ y))) = (M.op (σ x) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5791
  have eq5815 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5152 eq5811
    | exact resolve eq5811 eq5152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5152 eq5811
  have eq5825 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5815 eq14
    | exact resolve eq14 eq5815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5815
  have eq5827 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq5825
    | exact resolve eq5825 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5825
  have eq5830 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq5827
       have r₂ := eq27
       grind)
    | exact resolve eq5827 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5827
  have eq5832 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5830 eq177
    | exact resolve eq177 eq5830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq5834 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5830 eq1503
    | (have r₁ := eq1503
       have r₂ := eq5830
       grind)
    | exact resolve eq1503 eq5830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503 eq5830
  have eq5836 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq5834
  have eq6287 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5836 eq152
    | exact resolve eq152 eq5836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq6297 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq6287
    | exact resolve eq6287 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6287
  have eq6404 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 X0) (σ y)) (σ x)) ∨ x = (k x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6297 eq16
    | exact resolve eq16 eq6297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6297
  have eq6412 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5832 eq6404
    | exact resolve eq6404 eq5832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6404
  have eq6448 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1541
       have i₂ := eq6412
       grind)
    | exact superpose eq6412 eq1541
    | exact resolve eq1541 eq6412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1541 eq6412
  have eq6453 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq6448
  have eq6482 : ∀ X0 : G, x = (M.op X0 X0) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq539 y X0
       have i₂ := eq6453
       grind)
    | exact superpose eq6453 eq539
    | exact resolve eq539 eq6453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6500 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq676 y X0
       have i₂ := eq6453
       grind)
    | exact superpose eq6453 eq676
    | exact resolve eq676 eq6453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6513 : ∀ X0 X1 : G, (k x X1) = (k (M.op X0 X0) X1) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq1376 X0 X1 y
       have i₂ := eq6453
       grind)
    | exact superpose eq6453 eq1376
    | exact resolve eq1376 eq6453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6453
  have eq6546 : ∀ X0 : G, (M.op X0 X0) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq6513 eq6500
    | exact resolve eq6500 eq6513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6500 eq6513
  have eq6563 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6482 eq6546
    | exact resolve eq6546 eq6482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6546
  have eq6833 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq6563
       grind)
    | exact superpose eq6563 eq39
    | exact resolve eq39 eq6563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6563
  have eq6845 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6833
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6833
    | exact resolve eq6833 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6833
  have eq6854 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op X0 X0) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq6845 eq2882
    | (have j0 := eq2882 X0 (σ x)
       grind)
    | (have r₁ := eq2882 X0 (σ x)
       have r₂ := eq6845
       grind)
    | exact resolve eq2882 eq6845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6855 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6845 eq1602
    | (have j0 := eq1602 (σ x) (σ x)
       grind)
    | (have r₁ := eq1602 (σ x) (σ x)
       have r₂ := eq6845
       grind)
    | exact resolve eq1602 eq6845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6845
  have eq6856 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq6855
  have eq6857 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq6856
  have eq6858 : ∀ X0 : G, (σ x) = (M.op X0 X0) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq6854 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6854
  have eq6929 : x = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6857 eq6482
    | exact resolve eq6482 eq6857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6482 eq6857
  have eq6933 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (σ x) := by grind
  clear eq6929
  have eq7061 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq6933 eq5836
    | exact resolve eq5836 eq6933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6933
  have eq7064 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (σ x) := by grind
  clear eq7061
  have eq7069 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | (have j1 := eq1604 (σ x)
       grind)
    | (have r₁ := eq7064
       have r₂ := eq1604 (σ x)
       grind)
    | exact resolve eq7064 eq1604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1604 eq7064
  have eq7472 : ∀ X0 : G, (σ x) = (M.op X0 X0) ∨ x = (M.op x y) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq7069 eq539
    | exact resolve eq539 eq7069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7490 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (σ x)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq7069 eq676
    | exact resolve eq676 eq7069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq7503 : ∀ X0 X1 : G, (k (σ x) X1) = (k (M.op X0 X0) X1) ∨ x = (M.op x y) ∨ x = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq7069 eq1376
    | exact resolve eq1376 eq7069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1376 eq7069
  have eq7537 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq7503 eq7490
    | exact resolve eq7490 eq7503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7490 eq7503
  have eq7557 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq7472 eq7537
    | exact resolve eq7537 eq7472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7537
  have eq7812 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq7557 eq141
    | exact resolve eq141 eq7557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq7557
  have eq7823 : x = (k x x) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq29 eq7812
    | exact resolve eq7812 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7812
  have eq7834 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq1602 x x
       have i₂ := eq7823
       grind)
    | exact superpose eq7823 eq1602
    | (have j0 := eq1602 x x
       grind)
    | (have r₁ := eq1602 x x
       have r₂ := eq7823
       grind)
    | exact resolve eq1602 eq7823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7823
  have eq7835 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (σ x) := by grind
  clear eq7834
  have eq7836 : x = (M.op x x) ∨ x = (M.op x y) ∨ x = (σ x) := by grind
  clear eq7835
  have eq7841 : x = (σ x) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq7472 eq7836
    | exact resolve eq7836 eq7472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7472 eq7836
  have eq7842 : x = (σ x) ∨ x = (M.op x y) := by grind
  clear eq7841
  have eq7854 : (σ x) = (σ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22
       have i₂ := eq7842
       grind)
    | exact superpose eq7842 eq22
    | exact resolve eq22 eq7842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7855 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq7842
       grind)
    | exact superpose eq7842 eq35
    | exact resolve eq35 eq7842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq7867 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) := by grind
  have eq8829 : (σ (σ x)) = (k (σ x) (σ (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5836 eq7855
    | exact resolve eq7855 eq5836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5836 eq7855
  have eq8854 : (σ (σ x)) = (k (σ x) (σ (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq8829
  have eq8887 : (σ x) = (k (σ x) (σ (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq7854 eq8854
    | exact resolve eq8854 eq7854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8854
  have eq8894 : (σ x) = (k (σ x) (σ (σ x))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq6858 eq8887
    | (have j1 := eq6858 (σ y)
       grind)
    | exact resolve eq8887 eq6858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6858 eq8887
  have eq8897 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq7854 eq8894
    | exact resolve eq8894 eq7854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7854 eq8894
  have eq8898 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq2882 (σ y) (σ x)
       grind)
    | (have r₁ := eq8897
       have r₂ := eq2882 x (σ x)
       grind)
    | exact resolve eq8897 eq2882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2882 eq8897
  have eq8919 : ∀ X0 : G, (σ x) = (M.op X0 X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8898 eq539
    | exact resolve eq539 eq8898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8924 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (σ x)) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq8898 eq564
    | exact resolve eq564 eq8898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq8940 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ x) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq8898 eq721
    | exact resolve eq721 eq8898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq8968 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 X0) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8898 eq16
    | exact resolve eq16 eq8898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8898
  have eq8979 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5832 eq8968
    | exact resolve eq8968 eq5832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5832 eq8968
  have eq8995 : ∀ X1 : G, (M.op (M.op (σ x) X1) (σ x)) = X1 ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq8940 eq8924
    | exact resolve eq8924 eq8940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8924 eq8940
  have eq9023 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8979 eq31
    | exact resolve eq31 eq8979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8979
  have eq9063 : x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq9023
    | exact resolve eq9023 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9023
  have eq9076 : y = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7842 eq9063
    | exact resolve eq9063 eq7842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9063
  have eq9088 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (M.op x y)) x) = (M.op (M.op X0 X0) (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq182 X1 X0
       have i₂ := eq9076
       grind)
    | exact superpose eq9076 eq182
    | exact resolve eq182 eq9076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9076
  have eq9114 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op (M.op X1 X1) (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq7842 eq9088
    | exact resolve eq9088 eq7842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7842 eq9088
  have eq9121 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op (σ x) (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8919 eq9114
    | exact resolve eq9114 eq8919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9114
  have eq9123 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8919 eq9121
    | exact resolve eq9121 eq8919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9121
  have eq9125 : (σ x) = (M.op (M.op (σ x) (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8919 eq9123
    | exact resolve eq9123 eq8919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8919 eq9123
  have eq9126 : (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8995 eq9125
    | exact resolve eq9125 eq8995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8995 eq9125
  have eq9127 : x = (M.op x y) := by
    first
    | (have r₁ := eq9126
       have r₂ := eq7867
       grind)
    | exact resolve eq9126 eq7867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7867 eq9126
  have eq9130 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq9127
       grind)
    | exact superpose eq9127 eq18
    | exact resolve eq18 eq9127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq9131 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq9127
       grind)
    | exact superpose eq9127 eq22
    | exact resolve eq22 eq9127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq9133 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq9127
       grind)
    | exact superpose eq9127 eq39
    | exact resolve eq39 eq9127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq9134 : ∀ X0 X1 : G, (M.op (M.op X0 X0) y) = (M.op (M.op (M.op X1 X1) (M.op x y)) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq182 X1 X0
       have i₂ := eq9127
       grind)
    | exact superpose eq9127 eq182
    | exact resolve eq182 eq9127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq9135 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | (have i₁ := eq1502
       have i₂ := eq9127
       grind)
    | exact superpose eq9127 eq1502
    | (have r₁ := eq1502
       have r₂ := eq9127
       grind)
    | exact resolve eq1502 eq9127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1502
  have eq9137 : (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq9135
  have eq9139 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq9131 eq20
    | exact resolve eq20 eq9131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9207 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq9130 eq16
    | exact resolve eq16 eq9130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10713 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq9137 eq40
    | exact resolve eq40 eq9137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq9137
  have eq10719 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq10713
    | exact resolve eq10713 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10713
  have eq10722 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq9139 eq10719
    | exact resolve eq10719 eq9139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10719
  have eq10733 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq10722 eq1542
    | exact resolve eq1542 eq10722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1542
  have eq10744 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq10733
  have eq15432 : ∀ X0 X1 : G, y = (k (M.op X1 X1) (M.op (M.op (M.op X0 X0) (M.op x y)) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq752 x y X1
       have i₂ := eq9134 x X0
       grind)
    | exact superpose eq9134 eq752
    | exact resolve eq752 eq9134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9134
  have eq16734 : ∀ X0 : G, (σ x) = (M.op X0 X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq10744 eq539
    | exact resolve eq539 eq10744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16759 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (k (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq10744 eq925
    | exact resolve eq925 eq10744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925 eq10744
  have eq16825 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq10722 eq16759
    | exact resolve eq16759 eq10722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10722 eq16759
  have eq16856 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq16734 eq16825
    | exact resolve eq16825 eq16734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16825
  have eq16874 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq16734 eq16856
    | exact resolve eq16856 eq16734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16734 eq16856
  have eq16996 : ∀ X0 : G, y = (k (M.op X0 X0) (M.op (M.op (M.op x y) (M.op x y)) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq15432 y X0
       have i₂ := eq16874
       grind)
    | exact superpose eq16874 eq15432
    | exact resolve eq15432 eq16874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16874
  have eq17028 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16996 x
       have i₂ := eq752 sF0 sF0 x
       grind)
    | (have i₁ := eq16996 x
       have i₂ := eq752 x (k (M.op x x) (M.op (M.op sF0 sF0) sF0)) x
       grind)
    | exact superpose eq752 eq16996
    | exact resolve eq16996 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752 eq16996
  have eq17065 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17028 eq27
    | exact resolve eq27 eq17028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17028
  have eq17072 : (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq17065
       have r₂ := eq9139
       grind)
    | exact resolve eq17065 eq9139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17065
  have eq17074 : y = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17072 eq31
    | exact resolve eq31 eq17072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq17072
  have eq17111 : x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq17074
    | exact resolve eq17074 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq17074
  have eq17123 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17111
       have i₂ := eq9127
       grind)
    | exact superpose eq9127 eq17111
    | exact resolve eq17111 eq9127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9127 eq17111
  have eq17124 : y = (M.op x y) := by grind
  clear eq17123
  have eq17127 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq17124
       grind)
    | exact superpose eq17124 eq24
    | exact resolve eq24 eq17124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq17162 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq9130
       have i₂ := eq17124
       grind)
    | exact superpose eq17124 eq9130
    | exact resolve eq9130 eq17124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9130
  have eq17165 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op X0 X0) (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq9207 X0
       have i₂ := eq17124
       grind)
    | exact superpose eq17124 eq9207
    | exact resolve eq9207 eq17124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9207
  have eq17181 : (σ x) = (σ y) := by
    first
    | exact superpose eq9131 eq17127
    | exact resolve eq17127 eq9131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9131 eq17127
  have eq17184 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq17181 eq26
    | exact resolve eq26 eq17181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq17181
  have eq17258 : ∀ X0 : G, (M.op x y) = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq17162 eq539
    | exact resolve eq539 eq17162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17327 : ∀ X0 : G, y = (k (M.op x y) (M.op (M.op (M.op X0 X0) (M.op x y)) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq17162 eq15432
    | exact resolve eq15432 eq17162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15432 eq17162
  have eq17341 : y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq17165 eq17327
    | exact resolve eq17327 eq17165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17165 eq17327
  have eq17371 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq17341
       have i₂ := eq17124
       grind)
    | exact superpose eq17124 eq17341
    | exact resolve eq17341 eq17124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17124 eq17341
  have eq17446 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq17184 eq539
    | exact resolve eq539 eq17184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539 eq17184
  have eq17577 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17446 x
       have i₂ := eq17258 x
       grind)
    | exact superpose eq17258 eq17446
    | exact resolve eq17446 eq17258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17446
  have eq17670 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq17577 eq27
    | exact resolve eq27 eq17577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq17577
  have eq17688 : (M.op x y) ≠ (σ x) := by
    first
    | exact superpose eq9139 eq17670
    | exact resolve eq17670 eq9139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17670
  have eq18110 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq17371 eq9133
    | exact resolve eq9133 eq17371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9133 eq17371
  have eq18128 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq18110
    | exact resolve eq18110 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq18110
  have eq18134 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq9139 eq18128
    | exact resolve eq18128 eq9139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9139 eq18128
  have eq18158 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18134 eq1602
    | (have j0 := eq1602 (σ x) (σ x)
       grind)
    | (have r₁ := eq1602 (σ x) (σ x)
       have r₂ := eq18134
       grind)
    | exact resolve eq1602 eq18134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1602 eq18134
  have eq18159 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq18158
  have eq18160 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq18159
  have eq18164 : (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq18160
       have i₂ := eq17258 sF2
       grind)
    | exact superpose eq17258 eq18160
    | exact resolve eq18160 eq17258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17258 eq18160
  have eq18175 : False := by grind
  exact eq18175

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pxy_pyx_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
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
  clear eq48
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
  have eq178 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq176 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X0 X2 (M.op (M.op X1 X1) (M.op X2 X2))
       have i₂ := eq16 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq16 eq176
    | exact resolve eq176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq540 X0 X2
       grind)
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq540 X2 X0
       grind)
    | exact superpose eq540 eq16
    | exact resolve eq16 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X1 X0 (M.op X1 (M.op X0 X0))
       have i₂ := eq540 X2 (M.op X1 (M.op X0 X0))
       grind)
    | (have i₁ := eq176 X1 X0 (M.op X1 (M.op X0 X0))
       have i₂ := eq540 (M.op X1 (M.op X0 X0)) X2
       grind)
    | exact superpose eq540 eq176
    | exact resolve eq176 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq571 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq181 X1
       have i₂ := eq540 X0 X1
       grind)
    | (have i₁ := eq181 X0
       have i₂ := eq540 X0 X1
       grind)
    | exact superpose eq540 eq181
    | exact resolve eq181 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : (σ x) = (M.op (k (M.op (σ y) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq178 sF3
       have i₂ := eq181 sF3
       grind)
    | exact superpose eq181 eq178
    | exact resolve eq178 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq181
  have eq1237 : (M.op x y) = (k x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1239 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF2 sF3
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1241 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1291 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1237
       grind)
    | exact superpose eq1237 eq41
    | exact resolve eq41 eq1237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237
  have eq1292 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1291
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1291
    | exact resolve eq1291 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1291
  have eq1294 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1292
    | exact resolve eq1292 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292
  have eq1304 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1294 eq1239
    | exact resolve eq1239 eq1294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239 eq1294
  have eq1311 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1304
       have r₂ := eq27
       grind)
    | exact resolve eq1304 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304
  have eq1327 : ∀ X0 : G, (σ y) = (M.op X0 X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1311 eq540
    | exact resolve eq540 eq1311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1329 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (σ y)) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq1311 eq541
    | exact resolve eq541 eq1311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1311
  have eq1354 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X1 X1) (σ y)) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq1329 X0 X0
       have i₂ := eq571 X0 sF3
       grind)
    | exact superpose eq571 eq1329
    | exact resolve eq1329 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329
  have eq1363 : ∀ X0 : G, (M.op X0 X0) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1327 eq1354
    | exact resolve eq1354 eq1327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1354
  have eq1366 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1327 eq1363
    | exact resolve eq1363 eq1327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327 eq1363
  have eq1470 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1366 eq153
    | exact resolve eq153 eq1366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq1366
  have eq1473 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq32 eq1470
    | exact resolve eq1470 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1470
  have eq1476 : y = (M.op y y) := by
    first
    | (have j1 := eq1241 y
       grind)
    | (have r₁ := eq1473
       have r₂ := eq1241 y
       grind)
    | exact resolve eq1473 eq1241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq1492 : ∀ X0 : G, y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq540 y X0
       have i₂ := eq1476
       grind)
    | exact superpose eq1476 eq540
    | exact resolve eq540 eq1476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq1494 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X1) y) := by
    intro X0 X1
    first
    | (have i₁ := eq541 X0 X1 y
       have i₂ := eq1476
       grind)
    | exact superpose eq1476 eq541
    | exact resolve eq541 eq1476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1498 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq567 X1 X0 y
       have i₂ := eq1476
       grind)
    | exact superpose eq1476 eq567
    | exact resolve eq567 eq1476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq1501 : ∀ X0 : G, (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq571 y x
       have i₂ := eq1476
       grind)
    | exact superpose eq1476 eq571
    | exact resolve eq571 eq1476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1476
  have eq1516 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X1 X1) y) := by
    intro X0 X1
    first
    | (have i₁ := eq1494 X0 X1
       have i₂ := eq571 X1 y
       grind)
    | exact superpose eq571 eq1494
    | exact resolve eq1494 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1494
  have eq1526 : ∀ X0 : G, (M.op X0 X0) = (k y y) := by
    intro X0
    first
    | (have i₁ := eq1516 X0 x
       have i₂ := eq1492 x
       grind)
    | exact superpose eq1492 eq1516
    | exact resolve eq1516 eq1492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1516
  have eq1528 : y = (k y y) := by
    first
    | (have i₁ := eq1526 x
       have i₂ := eq1492 x
       grind)
    | exact superpose eq1492 eq1526
    | exact resolve eq1526 eq1492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526
  have eq1637 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq1528
       grind)
    | exact superpose eq1528 eq41
    | exact resolve eq41 eq1528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq1640 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1637
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1637
    | exact resolve eq1637 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1637
  have eq1651 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1640 eq1241
    | (have j0 := eq1241 (σ y)
       grind)
    | (have r₁ := eq1241 (σ y)
       have r₂ := eq1640
       grind)
    | exact resolve eq1241 eq1640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241
  have eq1652 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1651
  have eq1653 : y = (σ y) := by
    first
    | (have i₁ := eq1652
       have i₂ := eq1492 sF3
       grind)
    | exact superpose eq1492 eq1652
    | exact resolve eq1652 eq1492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1652
  have eq1657 : (M.op x y) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1653
       grind)
    | exact superpose eq1653 eq18
    | exact resolve eq18 eq1653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1766 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq1501 X0
       have i₂ := eq1653
       grind)
    | exact superpose eq1653 eq1501
    | exact resolve eq1501 eq1653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1787 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (k y y)) := by
    intro X0 X1
    first
    | (have i₁ := eq541 X0 X1 y
       have i₂ := eq1501 y
       grind)
    | exact superpose eq1501 eq541
    | exact resolve eq541 eq1501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq1788 : ∀ X0 X1 : G, (M.op (M.op (k y y) X0) (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq565 X1 y X0
       have i₂ := eq1501 y
       grind)
    | exact superpose eq1501 eq565
    | exact resolve eq565 eq1501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565 eq1501
  have eq1831 : ∀ X0 : G, (M.op (M.op (k y y) X0) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq1788 X0 x
       have i₂ := eq1498 (M.op (k y y) X0) x
       grind)
    | exact superpose eq1498 eq1788
    | exact resolve eq1788 eq1498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498 eq1788
  have eq1832 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X1 X1) (k y y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1787 X0 X1
       have i₂ := eq571 X1 (k y y)
       grind)
    | exact superpose eq571 eq1787
    | exact resolve eq1787 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571 eq1787
  have eq1862 : ∀ X0 : G, (M.op (M.op (k (σ y) (σ y)) X0) (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1831 X0
       have i₂ := eq1653
       grind)
    | exact superpose eq1653 eq1831
    | exact resolve eq1831 eq1653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1831
  have eq1863 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X1 X1) y) := by
    intro X0 X1
    first
    | (have i₁ := eq1832 X0 X1
       have i₂ := eq1528
       grind)
    | exact superpose eq1528 eq1832
    | exact resolve eq1832 eq1528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1528 eq1832
  have eq1883 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq1640 eq1862
    | exact resolve eq1862 eq1640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1862
  have eq1884 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X1 X1) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1863 X0 X1
       have i₂ := eq1653
       grind)
    | exact superpose eq1653 eq1863
    | exact resolve eq1863 eq1653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1863
  have eq1895 : ∀ X0 : G, (M.op (k (σ y) X0) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq1766 eq1883
    | exact resolve eq1883 eq1766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1883
  have eq1896 : ∀ X0 : G, (M.op X0 X0) = (k y (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1884 X0 x
       have i₂ := eq1492 x
       grind)
    | exact superpose eq1492 eq1884
    | exact resolve eq1884 eq1492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1492 eq1884
  have eq1902 : ∀ X0 : G, (M.op X0 X0) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1896 X0
       have i₂ := eq1653
       grind)
    | exact superpose eq1653 eq1896
    | exact resolve eq1896 eq1653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1896
  have eq1905 : ∀ X0 : G, (σ y) = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq1640 eq1902
    | exact resolve eq1902 eq1640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1902
  have eq1964 : (σ x) = (M.op (k (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq575
       have i₂ := eq1905 sF3
       grind)
    | exact superpose eq1905 eq575
    | exact resolve eq575 eq1905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq1905
  have eq1965 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1640 eq1964
    | exact resolve eq1964 eq1640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1640 eq1964
  have eq1998 : (σ x) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1766 eq1965
    | exact resolve eq1965 eq1766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1766 eq1965
  have eq2060 : (τ (σ x)) = (k y (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1998 eq108
    | exact resolve eq108 eq1998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq1998
  have eq2061 : (τ (σ x)) = (k (σ y) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq2060
       have i₂ := eq1653
       grind)
    | exact superpose eq1653 eq2060
    | exact resolve eq2060 eq1653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1653 eq2060
  have eq2062 : x = (k (σ y) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq30 eq2061
    | exact resolve eq2061 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2061
  have eq3019 : (τ (M.op (σ x) (σ y))) = (M.op x (σ y)) := by
    first
    | exact superpose eq2062 eq1895
    | exact resolve eq1895 eq2062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1895 eq2062
  have eq3036 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1657 eq3019
    | exact resolve eq3019 eq1657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1657 eq3019
  have eq3055 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3036 eq14
    | exact resolve eq14 eq3036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3036
  have eq3056 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq3055
    | exact resolve eq3055 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3055
  have eq3059 : False := by grind
  exact eq3059

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxy_pxx_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
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
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq53 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) X1)) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    grind
  have eq76 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
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
  have eq109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq103
    | exact resolve eq103 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq109
    | exact resolve eq109 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq341 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq53 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq76 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq790 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 (M.op x (M.op (M.op X0 X0) (M.op X1 X1)))
       have i₂ := eq53 (M.op X0 X0) X1 x
       grind)
    | exact superpose eq53 eq66
    | exact resolve eq66 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq66
  have eq15085 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq110 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15086 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq15085
    | exact resolve eq15085 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15085
  have eq15097 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq15086
       have r₂ := eq29
       grind)
    | exact resolve eq15086 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15086
  have eq15103 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq15097
  have eq15178 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq15103
    | exact resolve eq15103 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15103
  have eq16521 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq15178 eq110
    | exact resolve eq110 eq15178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq15178
  have eq16530 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq16521
  have eq16533 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq16530
       have r₂ := eq29
       grind)
    | exact resolve eq16530 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16530
  have eq16540 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq16533
  have eq16620 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16540
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq16540
    | exact resolve eq16540 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16540
  have eq17652 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq16620
       grind)
    | exact superpose eq16620 eq46
    | exact resolve eq46 eq16620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq16620
  have eq17670 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq22 eq17652
    | exact resolve eq17652 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17652
  have eq17723 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17670 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq17670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17724 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq17723
  have eq17728 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq28 eq17724
    | exact resolve eq17724 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17724
  have eq17739 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq17728
       have r₂ := eq29
       grind)
    | exact resolve eq17728 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17728
  have eq17796 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq17739
  have eq17879 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28 eq17796
    | exact resolve eq17796 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17796
  have eq20228 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq17879 eq17670
    | exact resolve eq17670 eq17879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17670 eq17879
  have eq20233 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq20228
  have eq20239 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq20233
       have r₂ := eq29
       grind)
    | exact resolve eq20233 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20233
  have eq20448 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq20239 eq31
    | exact resolve eq31 eq20239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq20239
  have eq20570 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq20448
    | exact resolve eq20448 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq20448
  have eq20571 : x = y := by grind
  clear eq20570
  have eq20572 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq20571
       grind)
    | exact superpose eq20571 eq20
    | exact resolve eq20 eq20571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq20573 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq20571
       grind)
    | exact superpose eq20571 eq26
    | exact resolve eq26 eq20571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq20571
  have eq20681 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq20573
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20573
    | exact resolve eq20573 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq20573
  have eq20682 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20681 eq28
    | exact resolve eq28 eq20681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq20681
  have eq21505 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq20572
       have i₂ := eq341 X0 x
       grind)
    | (have i₁ := eq20572
       have i₂ := eq341 x X0
       grind)
    | exact superpose eq341 eq20572
    | exact resolve eq20572 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq21563 : ∀ X0 : G, (k (M.op x y) X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq790 X0 x
       have i₂ := eq20572
       grind)
    | exact superpose eq20572 eq790
    | exact resolve eq790 eq20572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790 eq20572
  have eq21742 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20682 eq21505
    | exact resolve eq21505 eq20682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20682
  have eq22199 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq21742 eq29
    | exact resolve eq29 eq21742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq21742
  have eq24243 : (σ (M.op x y)) ≠ (σ (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21563 eq573
    | (have j0 := eq573 (M.op x y)
       grind)
    | exact resolve eq573 eq21563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573 eq21563
  have eq24340 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq24243
       have i₂ := eq21505 sF0
       grind)
    | exact superpose eq21505 eq24243
    | exact resolve eq24243 eq21505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24243
  have eq24341 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq24340
  have eq24381 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq24341
       have i₂ := eq21505 (σ sF0)
       grind)
    | exact superpose eq21505 eq24341
    | exact resolve eq24341 eq21505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21505 eq24341
  have eq24405 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq22 eq24381
    | exact resolve eq24381 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24381
  have eq24422 : False := by grind
  exact eq24422

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pyx_pyy_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq47 : ∀ X0 : G, (σ (k X0 (k x x))) = (k (σ X0) (k (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq10
    | exact resolve eq10 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  clear eq43
  have eq51 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X1) ∨ (k X2 (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X0 X0) X1)
       have i₂ := eq14 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 (M.op (M.op X0 X0) X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq80
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq80
    | exact resolve eq80 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq85
    | exact resolve eq85 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq87
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq87
    | exact resolve eq87 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq99 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq110 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq110 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq110 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq116 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq111 y
       grind)
    | exact superpose eq111 eq72
    | exact resolve eq72 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq117 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq111 sF2
       grind)
    | exact superpose eq111 eq49
    | exact resolve eq49 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq118 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq117
       have i₂ := eq111 x
       grind)
    | exact superpose eq111 eq117
    | exact resolve eq117 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq119 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq116
       have i₂ := eq111 sF3
       grind)
    | exact superpose eq111 eq116
    | exact resolve eq116 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq125 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq99
       have i₂ := eq111 sF3
       grind)
    | exact superpose eq111 eq99
    | exact resolve eq99 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq126 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq125
       have i₂ := eq111 y
       grind)
    | exact superpose eq111 eq125
    | exact resolve eq125 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq431 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq51 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq434 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) X0) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op X0 (M.op X2 (M.op X3 X3)))
       have i₂ := eq51 X2 X3 X0
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) = (M.op (M.op (M.op X4 X4) X0) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq54 X2 X4 (M.op X0 (M.op X2 (M.op X3 X3))) X1
       have i₂ := eq51 X2 X3 X0
       grind)
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq54
  have eq591 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) X2) = (k X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X0 (M.op X0 X0) X2
       have i₂ := eq431 X0 (M.op X0 X0)
       grind)
    | (have i₁ := eq64 X0 (M.op X0 X0) X2
       have i₂ := eq431 (M.op X0 X0) X1
       grind)
    | exact superpose eq431 eq64
    | (have r₁ := eq64 X1 (M.op X1 X1) X2
       have r₂ := eq431 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq64 X0 (M.op X0 X0) X2
       have r₂ := eq431 X0 (M.op X0 X0)
       grind)
    | exact resolve eq64 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq592 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = (k X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have j0 := eq591 X0 x X2
       grind)
    | (have r₁ := eq591 X0 x X2
       have r₂ := eq431 X0 x
       grind)
    | (have r₁ := eq591 x X0 X2
       have r₂ := eq431 X0 x
       grind)
    | exact resolve eq591 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq5764 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X2) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq434 X1 x X2 x
       have i₂ := eq513 X1 x X2 x X0
       grind)
    | exact superpose eq513 eq434
    | exact resolve eq434 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq6264 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5764 (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) (M.op X0 (M.op X1 X1)) X2
       have i₂ := eq434 (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)) X0 X1
       grind)
    | exact superpose eq434 eq5764
    | exact resolve eq5764 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434 eq5764
  have eq7097 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq6264 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6264
    | (have j0 := eq6264 x X0 y
       grind)
    | exact resolve eq6264 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7098 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq26 eq6264
    | (have j0 := eq6264 (σ x) X0 (σ y)
       grind)
    | exact resolve eq6264 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28463 : ∀ X0 : G, (σ (k X0 (k x x))) = (k (σ X0) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq111 sF2
       grind)
    | exact superpose eq111 eq47
    | exact resolve eq47 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq28464 : ∀ X0 : G, (σ (k X0 (k x x))) = (M.op (M.op (σ x) (σ x)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq28463 X0
       have i₂ := eq592 sF2 (σ X0)
       grind)
    | exact superpose eq592 eq28463
    | exact resolve eq28463 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28463
  have eq28465 : ∀ X0 : G, (σ (k X0 (M.op x x))) = (M.op (M.op (σ x) (σ x)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq28464 X0
       have i₂ := eq111 x
       grind)
    | exact superpose eq111 eq28464
    | exact resolve eq28464 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq28464
  have eq28466 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (σ X0)) = (σ (M.op (M.op x x) X0)) := by
    intro X0
    first
    | (have i₁ := eq28465 X0
       have i₂ := eq592 x X0
       grind)
    | exact superpose eq592 eq28465
    | exact resolve eq28465 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592 eq28465
  have eq34703 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op x x) X0)) (M.op X1 (σ X0))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq28466 eq14
    | exact resolve eq14 eq28466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28466
  have eq42190 : ∀ X0 X1 : G, (M.op (σ x) (M.op X1 (σ (M.op x (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34703 (M.op x (M.op X0 X0)) X1
       have i₂ := eq6264 x X0 x
       grind)
    | exact superpose eq6264 eq34703
    | exact resolve eq34703 eq6264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34703
  have eq42438 : ∀ X0 X1 : G, (M.op (σ x) (M.op X1 (σ (M.op x (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42190 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq42190
    | (have j0 := eq42190 X0 X1
       grind)
    | exact resolve eq42190 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42190
  have eq42781 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X0)) = (σ (M.op x (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq42438 X1 (σ (M.op x (M.op X1 X1)))
       have i₂ := eq431 X0 (σ (M.op x (M.op X1 X1)))
       grind)
    | (have i₁ := eq42438 X1 (σ (M.op x (M.op X1 X1)))
       have i₂ := eq431 (σ (M.op x (M.op X1 X1))) X0
       grind)
    | exact superpose eq431 eq42438
    | exact resolve eq42438 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431 eq42438
  have eq45121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq88 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq45122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq45121
    | exact resolve eq45121 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45121
  have eq45133 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq45122
       have r₂ := eq27
       grind)
    | exact resolve eq45122 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45122
  have eq45137 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq45133
    | exact resolve eq45133 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45133
  have eq45322 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X0))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq45137 eq6264
    | exact resolve eq6264 eq45137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45137
  have eq45326 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq7098 eq45322
    | exact resolve eq45322 eq7098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7098 eq45322
  have eq45355 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq45326 eq126
    | exact resolve eq126 eq45326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq45326
  have eq45566 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq45355
    | exact resolve eq45355 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45355
  have eq45567 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq45566
  have eq45748 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x (M.op X0 X0))) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq6264 x X0 x
       have i₂ := eq45567
       grind)
    | exact superpose eq45567 eq6264
    | exact resolve eq6264 eq45567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6264 eq45567
  have eq45752 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq7097 eq45748
    | exact resolve eq45748 eq7097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7097 eq45748
  have eq45800 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq119
       have i₂ := eq45752
       grind)
    | exact superpose eq45752 eq119
    | exact resolve eq119 eq45752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq45949 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq42781 X0 y
       have i₂ := eq45752
       grind)
    | exact superpose eq45752 eq42781
    | exact resolve eq42781 eq45752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42781 eq45752
  have eq45978 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq45949 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq45949
    | (have j0 := eq45949 X0
       grind)
    | exact resolve eq45949 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45949
  have eq46001 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq45800
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq45800
    | exact resolve eq45800 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45800
  have eq46004 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq20 eq45978
    | (have j0 := eq45978 X0
       grind)
    | exact resolve eq45978 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45978
  have eq97581 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq46001 eq46004
    | exact resolve eq46004 eq46001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46001 eq46004
  have eq97666 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq97581
  have eq97721 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq97666
    | exact resolve eq97666 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97666
  have eq97750 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq97721
       have r₂ := eq27
       grind)
    | exact resolve eq97721 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97721
  have eq97764 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq97750 eq29
    | exact resolve eq29 eq97750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq97750
  have eq98104 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq97764
    | exact resolve eq97764 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq97764
  have eq98105 : x = y := by grind
  clear eq98104
  have eq98134 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq98105
       grind)
    | exact superpose eq98105 eq18
    | exact resolve eq18 eq98105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq98135 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq98105
       grind)
    | exact superpose eq98105 eq24
    | exact resolve eq24 eq98105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq98105
  have eq98283 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq98135
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq98135
    | exact resolve eq98135 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq98135
  have eq98340 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq98283 eq26
    | exact resolve eq26 eq98283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq98283
  have eq99032 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq98340 eq118
    | exact resolve eq118 eq98340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq98340
  have eq99355 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq99032
       have i₂ := eq98134
       grind)
    | exact superpose eq98134 eq99032
    | exact resolve eq99032 eq98134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98134 eq99032
  have eq99392 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq99355 eq15
    | exact resolve eq15 eq99355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99355
  have eq99478 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq99392
    | exact resolve eq99392 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq99392
  have eq99506 : False := by grind
  exact eq99506

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pyx_pxy_x_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq51 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
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
  have eq64 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X1) ∨ (k X2 (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X0 X0) X1)
       have i₂ := eq14 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 (M.op (M.op X0 X0) X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq102 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq113 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k (M.op (M.op X0 X0) X2) X1) = (M.op (M.op (M.op X0 X0) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X0 X0) X2) X1
       have i₂ := eq14 (M.op X0 X0) X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | (have r₁ := eq12 X1 (M.op (M.op X1 X1) X2)
       have r₂ := eq14 (M.op X1 X1) X1 X2
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 X1) X2) X1
       have r₂ := eq14 (M.op X1 X1) X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq114 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq114 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq114 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq127 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq102
       have i₂ := eq115 sF3
       grind)
    | exact superpose eq115 eq102
    | exact resolve eq102 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq128 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq127
       have i₂ := eq115 y
       grind)
    | exact superpose eq115 eq127
    | exact resolve eq127 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq137 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq138 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq139 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq138
       have i₂ := eq115 sF1
       grind)
    | exact superpose eq115 eq138
    | exact resolve eq138 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq142 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq139
       have i₂ := eq115 sF0
       grind)
    | exact superpose eq115 eq139
    | exact resolve eq139 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq139
  have eq433 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq51 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq939 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) X2) = (k X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X0 (M.op X0 X0) X2
       have i₂ := eq433 X0 (M.op X0 X0)
       grind)
    | (have i₁ := eq64 X0 (M.op X0 X0) X2
       have i₂ := eq433 (M.op X0 X0) X1
       grind)
    | exact superpose eq433 eq64
    | (have r₁ := eq64 X1 (M.op X1 X1) X2
       have r₂ := eq433 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq64 X0 (M.op X0 X0) X2
       have r₂ := eq433 X0 (M.op X0 X0)
       grind)
    | exact resolve eq64 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq944 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = (k X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have j0 := eq939 X0 x X2
       grind)
    | (have r₁ := eq939 X0 x X2
       have r₂ := eq433 X0 x
       grind)
    | (have r₁ := eq939 x X0 X2
       have r₂ := eq433 X0 x
       grind)
    | exact resolve eq939 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939
  have eq1757 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 X0) X2) X1) = (M.op (M.op (M.op X0 X0) X2) X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq113 X0 X1 X2
       grind)
    | (have r₁ := eq113 X0 X1 X2
       have r₂ := eq433 X0 X1
       grind)
    | (have r₁ := eq113 X1 X0 X2
       have r₂ := eq433 X0 X1
       grind)
    | exact resolve eq113 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq1775 : ∀ X0 X2 : G, (M.op X0 X2) = (k X0 X2) ∨ (M.op X2 X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq1757 (M.op x x) x (M.op X0 (M.op x x))
       have i₂ := eq14 X0 x (M.op x x)
       grind)
    | exact superpose eq14 eq1757
    | (have j0 := eq1757 X0 X2 X2
       grind)
    | exact resolve eq1757 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1757
  have eq1851 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1775 x y
       grind)
    | exact superpose eq1775 eq44
    | (have j1 := eq1775 x y
       grind)
    | exact resolve eq44 eq1775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq1870 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1851
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1851
    | exact resolve eq1851 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1851
  have eq1872 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1870
    | exact resolve eq1870 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1870
  have eq1875 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1872 eq1775
    | (have j0 := eq1775 x (σ y)
       grind)
    | exact resolve eq1775 eq1872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775 eq1872
  have eq1876 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq1875
    | exact resolve eq1875 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1875
  have eq1879 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1876
       have r₂ := eq27
       grind)
    | exact resolve eq1876 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1876
  have eq1886 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1879 eq128
    | exact resolve eq128 eq1879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq1879
  have eq1922 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq1886
    | exact resolve eq1886 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1886
  have eq1923 : y = (M.op y y) := by grind
  clear eq1922
  have eq1924 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq1923
       have i₂ := eq433 X0 y
       grind)
    | (have i₁ := eq1923
       have i₂ := eq433 y X0
       grind)
    | exact superpose eq433 eq1923
    | exact resolve eq1923 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq1934 : x = (M.op (M.op y y) (M.op x y)) := by
    first
    | (have i₁ := eq52 y
       have i₂ := eq1923
       grind)
    | exact superpose eq1923 eq52
    | exact resolve eq52 eq1923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1958 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq944 y x
       have i₂ := eq1923
       grind)
    | exact superpose eq1923 eq944
    | exact resolve eq944 eq1923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq1964 : x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq1934
       have i₂ := eq1923
       grind)
    | exact superpose eq1923 eq1934
    | exact resolve eq1934 eq1923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1923 eq1934
  have eq2021 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 X1
       have i₂ := eq1924 X1
       grind)
    | exact superpose eq1924 eq14
    | exact resolve eq14 eq1924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2045 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq142
       have i₂ := eq1924 sF0
       grind)
    | exact superpose eq1924 eq142
    | exact resolve eq142 eq1924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq2053 : y = (σ y) := by
    first
    | (have i₁ := eq2045
       have i₂ := eq1924 sF1
       grind)
    | exact superpose eq1924 eq2045
    | exact resolve eq2045 eq1924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2045
  have eq2066 : ∀ X1 : G, (M.op (M.op y X1) y) = X1 := by
    intro X1
    first
    | (have i₁ := eq2021 x X1
       have i₂ := eq1924 x
       grind)
    | exact superpose eq1924 eq2021
    | exact resolve eq2021 eq1924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1924 eq2021
  have eq2092 : y = (σ y) := by
    first
    | (have i₁ := eq2053
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2053
    | exact resolve eq2053 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2053
  have eq2111 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq2092 eq26
    | exact resolve eq26 eq2092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2331 : (k (σ (M.op x y)) (σ y)) = (σ (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq137
       have i₂ := eq1958 sF0
       grind)
    | exact superpose eq1958 eq137
    | exact resolve eq137 eq1958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq2338 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1964 eq2331
    | exact resolve eq2331 eq1964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1964 eq2331
  have eq2345 : (σ x) = (k (σ (M.op x y)) y) := by
    first
    | exact superpose eq2092 eq2338
    | exact resolve eq2338 eq2092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2092 eq2338
  have eq2350 : (σ x) = (M.op y (σ (M.op x y))) := by
    first
    | (have i₁ := eq2345
       have i₂ := eq1958 sF1
       grind)
    | exact superpose eq1958 eq2345
    | exact resolve eq2345 eq1958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1958 eq2345
  have eq2351 : (σ x) = (M.op y (σ (M.op x y))) := by
    first
    | (have i₁ := eq2350
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2350
    | exact resolve eq2350 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2350
  have eq2580 : (σ (M.op x y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq2351 eq2066
    | exact resolve eq2066 eq2351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2066 eq2351
  have eq2617 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2111 eq2580
    | exact resolve eq2580 eq2111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2111 eq2580
  have eq2619 : False := by grind
  exact eq2619

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyx_pyy_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq175 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
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
  have eq177 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq538 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq175 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq175 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq175 eq175
    | exact resolve eq175 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq558 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X2 X1) = (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq538 X0 X1
       grind)
    | (have i₁ := eq13 X2 X1
       have i₂ := eq538 X1 X0
       grind)
    | exact superpose eq538 eq13
    | (have j0 := eq13 X2 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq538 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq538 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq929 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq558 X0 (M.op X1 X1) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq957 : ∀ X0 X1 X2 : G, (M.op (k X0 (M.op X1 X1)) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X0
       have i₂ := eq929 X0 X1
       grind)
    | exact superpose eq929 eq16
    | exact resolve eq16 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq963 : ∀ X0 : G, (σ x) = (M.op (k (σ y) (M.op X0 X0)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq177 x
       have i₂ := eq929 sF3 x
       grind)
    | exact superpose eq929 eq177
    | exact resolve eq177 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq1426 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X1
       have i₂ := eq538 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq538 X0 X1
       grind)
    | exact superpose eq538 eq11
    | (have j0 := eq11 X0 (k X1 X1)
       grind)
    | exact resolve eq11 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1449 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq538 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq538
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq538 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1499 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq1500 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  clear eq26
  have eq1502 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1503 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1502 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1502
  have eq1528 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1449 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449
  have eq1535 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1426 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426
  have eq2005 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1503 X1
       have i₂ := eq1528 X1 X0
       grind)
    | exact superpose eq1528 eq1503
    | (have j0 := eq1503 X1
       have j1 := eq1528 X1 X1
       grind)
    | (have r₁ := eq1503 (M.op X1 X1)
       have r₂ := eq1528 (M.op X1 X1) X1
       grind)
    | exact resolve eq1503 eq1528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1528
  have eq2021 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2005 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2005
  have eq2178 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1535 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535
  have eq3802 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1499
       grind)
    | exact superpose eq1499 eq40
    | exact resolve eq40 eq1499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1499
  have eq3803 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq2021 x y
       grind)
    | (have r₁ := eq3802
       have r₂ := eq2021 x y
       grind)
    | (have r₁ := eq3802
       have r₂ := eq2021 y y
       grind)
    | exact resolve eq3802 eq2021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3802
  have eq3805 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3803
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3803
    | exact resolve eq3803 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3803
  have eq3807 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq3805
    | exact resolve eq3805 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3805
  have eq5104 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1500 eq3807
    | exact resolve eq3807 eq1500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1500 eq3807
  have eq5111 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq2021 x y
       grind)
    | (have r₁ := eq5104
       have r₂ := eq2021 y y
       grind)
    | (have r₁ := eq5104
       have r₂ := eq2021 (σ x) (σ y)
       grind)
    | (have r₁ := eq5104
       have r₂ := eq2021 (σ y) (σ y)
       grind)
    | exact resolve eq5104 eq2021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2021 eq5104
  have eq5115 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq5111
       have r₂ := eq27
       grind)
    | exact resolve eq5111 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5111
  have eq5148 : ∀ X0 : G, y = (M.op y y) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | exact superpose eq5115 eq538
    | exact resolve eq538 eq5115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5115
  have eq5278 : ∀ X0 X1 : G, (M.op X1 X1) = (σ y) ∨ (M.op X0 X0) = y := by
    intro X0 X1
    first
    | (have i₁ := eq538 y X0
       have i₂ := eq5148 X1
       grind)
    | exact superpose eq5148 eq538
    | (have j1 := eq5148 X1
       grind)
    | exact resolve eq538 eq5148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538 eq5148
  have eq5560 : ∀ X0 X1 : G, (σ y) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq929 (M.op X0 X0) X0
       have i₂ := eq5278 X1 (M.op X0 X0)
       grind)
    | (have i₁ := eq929 (M.op X1 X1) X1
       have i₂ := eq5278 (M.op X1 X1) X1
       grind)
    | exact superpose eq5278 eq929
    | (have j1 := eq5278 X1 X1
       grind)
    | exact resolve eq929 eq5278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5567 : ∀ X1 : G, (σ y) = (k (σ y) (σ y)) ∨ (M.op X1 X1) = y := by
    intro X1
    first
    | exact superpose eq5278 eq5560
    | (have j0 := eq5560 x X1
       have j1 := eq5278 X1 X1
       grind)
    | exact resolve eq5560 eq5278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5278 eq5560
  have eq6223 : ∀ X0 : G, (τ (σ y)) = (k (τ (σ y)) y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | exact superpose eq5567 eq152
    | (have j1 := eq5567 X0
       grind)
    | exact resolve eq152 eq5567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5567
  have eq6229 : ∀ X0 : G, y = (k y y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | exact superpose eq31 eq6223
    | (have j0 := eq6223 X0
       grind)
    | exact resolve eq6223 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq6223
  have eq6232 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq6229 X0
       have j1 := eq2178 X0 y
       grind)
    | (have r₁ := eq6229 X0
       have r₂ := eq2178 X0 y
       grind)
    | exact resolve eq6229 eq2178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6229
  have eq6347 : ∀ X0 : G, y = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq929 (M.op X0 X0) X0
       have i₂ := eq6232 (M.op X0 X0)
       grind)
    | exact superpose eq6232 eq929
    | exact resolve eq929 eq6232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6353 : y = (k y y) := by
    first
    | (have i₁ := eq6347 x
       have i₂ := eq6232 x
       grind)
    | exact superpose eq6232 eq6347
    | exact resolve eq6347 eq6232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6347
  have eq6499 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq6353
       grind)
    | exact superpose eq6353 eq40
    | exact resolve eq40 eq6353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq6353
  have eq6505 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq6499
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6499
    | exact resolve eq6499 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq6499
  have eq6517 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | exact superpose eq6505 eq2178
    | (have j0 := eq2178 X0 (σ y)
       grind)
    | (have r₁ := eq2178 X0 (σ y)
       have r₂ := eq6505
       grind)
    | exact resolve eq2178 eq6505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2178
  have eq6518 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq6505 eq1503
    | (have j0 := eq1503 (σ y)
       grind)
    | (have r₁ := eq1503 (σ y)
       have r₂ := eq6505
       grind)
    | exact resolve eq1503 eq6505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503
  have eq6519 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6518
  have eq6520 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq6517 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6517
  have eq6521 : y = (σ y) := by
    first
    | (have i₁ := eq6519
       have i₂ := eq6232 sF3
       grind)
    | exact superpose eq6232 eq6519
    | exact resolve eq6519 eq6232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6519
  have eq6525 : (M.op x y) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq6521
       grind)
    | exact superpose eq6521 eq18
    | exact resolve eq18 eq6521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq6830 : ∀ X1 : G, (k X1 (σ y)) = (M.op (σ y) X1) := by
    intro X1
    first
    | (have i₁ := eq929 x x
       have i₂ := eq6520 x
       grind)
    | exact superpose eq6520 eq929
    | exact resolve eq929 eq6520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929
  have eq6842 : (σ x) = (M.op (k (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq963 x
       have i₂ := eq6520 x
       grind)
    | exact superpose eq6520 eq963
    | exact resolve eq963 eq6520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq6861 : ∀ X0 X1 : G, (M.op (k X0 (M.op X1 X1)) (σ y)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq957 X0 X1 X0
       have i₂ := eq6520 X0
       grind)
    | exact superpose eq6520 eq957
    | exact resolve eq957 eq6520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957 eq6520
  have eq6912 : ∀ X0 : G, (M.op (k X0 y) (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq6861 X0 x
       have i₂ := eq6232 x
       grind)
    | exact superpose eq6232 eq6861
    | exact resolve eq6861 eq6232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6232 eq6861
  have eq6925 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq6505 eq6842
    | exact resolve eq6842 eq6505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6505 eq6842
  have eq6994 : ∀ X0 : G, (M.op (k X0 (σ y)) (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq6912 X0
       have i₂ := eq6521
       grind)
    | exact superpose eq6521 eq6912
    | exact resolve eq6912 eq6521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6912
  have eq7004 : (σ x) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq6830 eq6925
    | exact resolve eq6925 eq6830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6830 eq6925
  have eq7222 : (τ (σ x)) = (k (τ (M.op (σ x) (σ y))) y) := by
    first
    | exact superpose eq7004 eq152
    | exact resolve eq152 eq7004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq7004
  have eq7223 : (τ (σ x)) = (k (τ (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq7222
       have i₂ := eq6521
       grind)
    | exact superpose eq6521 eq7222
    | exact resolve eq7222 eq6521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6521 eq7222
  have eq7224 : x = (k (τ (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq29 eq7223
    | exact resolve eq7223 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq7223
  have eq9209 : (τ (M.op (σ x) (σ y))) = (M.op x (σ y)) := by
    first
    | exact superpose eq7224 eq6994
    | exact resolve eq6994 eq7224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6994 eq7224
  have eq9234 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq6525 eq9209
    | exact resolve eq9209 eq6525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6525 eq9209
  have eq9258 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9234 eq14
    | exact resolve eq14 eq9234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9234
  have eq9259 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq9258
    | exact resolve eq9258 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq9258
  have eq9262 : False := by grind
  exact eq9262

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyx_pyy_pyx_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq63 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq9 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq63 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq63 eq63
    | exact resolve eq63 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq418 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 X0 X0
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq928 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X2 (σ X1)) = (σ (M.op X1 (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq418 X1 X2
       have i₂ := eq69 X0 X1
       grind)
    | (have i₁ := eq418 X1 X2
       have i₂ := eq69 X1 X0
       grind)
    | exact superpose eq69 eq418
    | (have j0 := eq418 X1 X2
       grind)
    | (have r₁ := eq418 (M.op X0 X0) X1
       have r₂ := eq69 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq418 (M.op X1 X1) X1
       have r₂ := eq69 (M.op X1 X1) X1
       grind)
    | exact resolve eq418 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq1618 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (M.op X0 X0) = X0 := by
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
  have eq1625 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1618 X0 X1
       have j1 := eq928 X0 X0 X1
       grind)
    | (have r₁ := eq1618 X1 X1
       have r₂ := eq928 (τ X1) X1 x
       grind)
    | (have r₁ := eq1618 (M.op X0 X0) X1
       have r₂ := eq928 X0 (M.op (τ X1) (τ X1)) x
       grind)
    | (have r₁ := eq1618 X1 X1
       have r₂ := eq928 X1 X1 x
       grind)
    | exact resolve eq1618 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928 eq1618
  have eq1648 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1625 X0 X1
       have j1 := eq418 X0 X1
       grind)
    | (have r₁ := eq1625 X0 X1
       have r₂ := eq418 X0 X1
       grind)
    | exact resolve eq1625 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418 eq1625
  have eq1650 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1648 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1648
    | exact resolve eq1648 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1648
  have eq5919 : ∀ X0 X1 : G, (τ (σ (M.op X0 X1))) = (k (τ (σ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X1) X0
       have i₂ := eq1650 X1 X0
       grind)
    | exact superpose eq1650 eq23
    | exact resolve eq23 eq1650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq5967 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5919 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5919
    | exact resolve eq5919 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5919
  have eq6006 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5967 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq5967
    | exact resolve eq5967 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5967
  have eq6109 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1650 X1 X0
       have i₂ := eq6006 (σ X0) (σ X1)
       grind)
    | exact superpose eq6006 eq1650
    | exact resolve eq1650 eq6006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1650 eq6006
  have eq8074 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6109 x y
       grind)
    | exact superpose eq6109 eq16
    | (have r₁ := eq16
       have r₂ := eq6109 x y
       grind)
    | exact resolve eq16 eq6109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6109
  have eq8144 : False := by grind
  exact eq8144
