import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_x_pyy_pxy_Equation3600 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3600 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq33 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 X0) X1) X3
       have i₂ := eq9 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq33 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq33
    | exact resolve eq33 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq39 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 x
       have i₂ := eq35 (M.op X0 X1) X0 x
       grind)
    | exact superpose eq35 eq9
    | exact resolve eq9 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X2 ∨ (M.op X0 X1) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X1) X2
       have i₂ := eq35 X0 X1 X2
       grind)
    | exact superpose eq35 eq12
    | (have j0 := eq12 (M.op X0 X1) X2
       grind)
    | (have r₁ := eq12 (M.op X0 X1) (M.op X0 X1)
       have r₂ := eq35 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X1 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X1 X0)
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq12
    | (have j0 := eq12 X1 (M.op X1 X0)
       grind)
    | (have r₁ := eq12 X1 (M.op X1 X1)
       have r₂ := eq39 X1 X1
       grind)
    | exact resolve eq12 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X1 X0) X1)) ∨ (M.op (M.op X1 X0) X1) = (M.op (M.op (M.op X1 X0) X1) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq59 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq60 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq59 X0
       have i₂ := eq35 (τ X0) (τ X0) (τ X0)
       grind)
    | exact superpose eq35 eq59
    | (have j0 := eq59 X0
       grind)
    | exact resolve eq59 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq61 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X1 X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       have j1 := eq12 (M.op X0 X1) (M.op (M.op X1 X0) X1)
       grind)
    | (have r₁ := eq57 X0 X1
       have r₂ := eq12 (M.op X0 X1) (M.op (M.op X1 X0) X1)
       grind)
    | exact resolve eq57 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq62 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq61
    | exact resolve eq61 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq63 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq75 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq29
    | exact resolve eq29 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (τ X1) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq90 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (M.op X1 (τ X0)) = X1 := by
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
  have eq236 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq51 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq271 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq236 (τ X0)
       grind)
    | exact superpose eq236 eq18
    | exact resolve eq18 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq272 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq271 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq271
    | exact resolve eq271 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq288 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq272 (τ X0)
       grind)
    | exact superpose eq272 eq18
    | exact resolve eq18 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq289 : ∀ X0 : G, (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq288 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq288
    | exact resolve eq288 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq303 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq88 X0 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq88
    | exact resolve eq88 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq320 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq88 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq321 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq320 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq323 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq318 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq325 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq323 X0
       have j1 := eq12 (σ (k X0 X0)) (σ X0)
       grind)
    | (have r₁ := eq323 X0
       have r₂ := eq12 (σ (k X0 X0)) (σ X0)
       grind)
    | (have r₁ := eq323 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | exact resolve eq323 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq336 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq325 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq325
    | (have j0 := eq325 X0
       grind)
    | exact resolve eq325 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq366 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))
       have i₂ := eq289 (τ X0)
       grind)
    | exact superpose eq289 eq18
    | exact resolve eq18 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq367 : ∀ X0 : G, (k X0 (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq366 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq366
    | exact resolve eq366 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq547 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq321 (M.op X0 X1)
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq321
    | (have j0 := eq321 (M.op X0 X1)
       grind)
    | exact resolve eq321 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq551 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq321 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq321
    | (have j0 := eq321 (τ X0)
       grind)
    | exact resolve eq321 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq552 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq547 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq554 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq551 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq551
    | (have j0 := eq551 X0
       grind)
    | exact resolve eq551 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq557 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq554 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq554
    | (have j0 := eq554 X0
       grind)
    | exact resolve eq554 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq569 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq336 (τ X0)
       grind)
    | exact superpose eq336 eq19
    | (have j1 := eq336 (τ X0)
       grind)
    | exact resolve eq19 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq601 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq569 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq569
    | (have j0 := eq569 X0
       grind)
    | exact resolve eq569 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq607 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq601 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq601
    | (have j0 := eq601 X0
       grind)
    | exact resolve eq601 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq612 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq607 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq607
    | (have j0 := eq607 X0
       grind)
    | exact resolve eq607 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq618 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq557 (τ X0)
       have i₂ := eq63 X0 X0
       grind)
    | exact superpose eq63 eq557
    | (have j0 := eq557 (τ X0)
       grind)
    | exact resolve eq557 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq635 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35 (σ (M.op X0 X1)) (σ (M.op X0 X1)) x
       have i₂ := eq552 X0 X1
       grind)
    | exact superpose eq552 eq35
    | exact resolve eq35 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq657 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq90 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq697 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq657 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq657
    | (have j0 := eq657 X0 X1
       grind)
    | exact resolve eq657 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq821 : ∀ X0 : G, (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) = (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq23 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0
       have i₂ := eq60 (σ X0)
       grind)
    | exact superpose eq60 eq23
    | (have j1 := eq60 (σ X0)
       grind)
    | exact resolve eq23 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq824 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ X0))) = (k (M.op (τ (σ X0)) (τ (σ X0))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq821 X0
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq821
    | (have j0 := eq821 X0
       grind)
    | exact resolve eq821 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq842 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq824 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq824
    | (have j0 := eq824 X0
       grind)
    | exact resolve eq824 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq852 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq842 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq842
    | (have j0 := eq842 X0
       grind)
    | exact resolve eq842 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq855 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq852 X0
       have j1 := eq41 X0 X0 X0
       grind)
    | (have r₁ := eq852 x
       have r₂ := eq41 x x x
       grind)
    | (have r₁ := eq852 (M.op X0 x)
       have r₂ := eq41 X0 x (M.op (M.op X0 x) (M.op X0 x))
       grind)
    | (have r₁ := eq852 x
       have r₂ := eq41 x x (k (M.op x x) x)
       grind)
    | exact resolve eq852 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq852
  have eq868 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq23 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq855 (σ X0)
       grind)
    | exact superpose eq855 eq23
    | exact resolve eq23 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq944 : ∀ X0 X1 X2 : G, (τ (k (k (σ X0) X1) X2)) = (k (M.op X0 (τ X1)) (τ X2)) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (τ X1) = (M.op (τ X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 (M.op X0 (τ X1)) X2
       have i₂ := eq86 X0 X1
       grind)
    | exact superpose eq86 eq29
    | (have j1 := eq86 X0 X1
       grind)
    | exact resolve eq29 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq86
  have eq954 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (k (M.op X0 (τ X1)) (τ X2)) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (τ X1) = (M.op (τ X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq944 X0 X1 X2
       have i₂ := eq75 X0 X1 X2
       grind)
    | exact superpose eq75 eq944
    | (have j0 := eq944 X0 X1 X2
       grind)
    | exact resolve eq944 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq944
  have eq1349 : ∀ X0 X1 : G, (τ (M.op X0 X1)) ≠ (τ (M.op X0 X1)) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq618 (M.op X0 X1)
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq618
    | (have j0 := eq618 (M.op X0 X1)
       grind)
    | exact resolve eq618 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq1358 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1349 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1349
  have eq1481 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35 (τ (M.op X0 X1)) (τ (M.op X0 X1)) x
       have i₂ := eq1358 X0 X1
       grind)
    | exact superpose eq1358 eq35
    | exact resolve eq35 eq1358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358
  have eq2872 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0))))))))
       have i₂ := eq367 (τ X0)
       grind)
    | exact superpose eq367 eq18
    | exact resolve eq18 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2884 : ∀ X0 : G, (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2872 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2872
    | exact resolve eq2872 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2872
  have eq2991 : ∀ X0 X1 X2 X3 : G, (k X0 (σ X1)) = (M.op X3 (k X0 (σ X1))) ∨ (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq35 (k X0 (σ X1)) (σ X2) X3
       have i₂ := eq303 X0 X1 X2
       grind)
    | exact superpose eq303 eq35
    | (have j1 := eq303 X0 X1 X2
       grind)
    | exact resolve eq35 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq29134 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq612 (τ X0)
       have i₂ := eq954 (τ X0) X0 X0
       grind)
    | exact superpose eq954 eq612
    | (have j0 := eq612 (τ X0)
       have j1 := eq954 (τ X0) X0 x
       grind)
    | exact resolve eq612 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612 eq954
  have eq29163 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq29134 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29134
  have eq29202 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq29163 X0
       have i₂ := eq63 X0 X0
       grind)
    | exact superpose eq63 eq29163
    | (have j0 := eq29163 X0
       grind)
    | exact resolve eq29163 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29163
  have eq29240 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq29202 X0
       have i₂ := eq855 (τ X0)
       grind)
    | exact superpose eq855 eq29202
    | (have j0 := eq29202 X0
       grind)
    | exact resolve eq29202 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855 eq29202
  have eq29346 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq62 (τ X0) (τ X0)
       have i₂ := eq29240 X0
       grind)
    | exact superpose eq29240 eq62
    | (have j1 := eq29240 X0
       grind)
    | exact resolve eq62 eq29240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29362 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq29240 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29240
  have eq29375 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq29346 X0
       have i₂ := eq63 X0 X0
       grind)
    | exact superpose eq63 eq29346
    | (have j0 := eq29346 X0
       grind)
    | exact resolve eq29346 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq29346
  have eq29396 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq29375 X0
       have j1 := eq29362 X0
       grind)
    | (have r₁ := eq29375 X0
       have r₂ := eq29362 X0
       grind)
    | exact resolve eq29375 eq29362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29362 eq29375
  have eq29410 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq29396 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29396
    | exact resolve eq29396 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29396
  have eq29661 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq29410 X0
       have i₂ := eq23 (σ X0) X0
       grind)
    | exact superpose eq23 eq29410
    | exact resolve eq29410 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq29410
  have eq29726 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq29661 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29661
    | exact resolve eq29661 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29661
  have eq30461 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq29726 (σ X0)
       grind)
    | exact superpose eq29726 eq15
    | exact resolve eq15 eq29726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30535 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq30461 X0
       have i₂ := eq29726 X0
       grind)
    | exact superpose eq29726 eq30461
    | exact resolve eq30461 eq29726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30461
  have eq32193 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 (σ X0) (σ X0)
       have i₂ := eq30535 X0
       grind)
    | exact superpose eq30535 eq39
    | exact resolve eq39 eq30535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132642 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (σ X2) = (M.op X0 X0) ∨ (M.op (σ X2) X0) = (σ (k X2 (k (τ X0) (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2991 X0 (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))) X2 x
       have i₂ := eq2884 X0
       grind)
    | exact superpose eq2884 eq2991
    | exact resolve eq2991 eq2884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2884 eq2991
  have eq132874 : ∀ X0 X1 X2 : G, (M.op (σ X2) X0) = (σ (k X2 (τ X0))) ∨ (M.op X1 X0) = X0 ∨ (σ X2) = (M.op X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq132642 X0 X1 X2
       have i₂ := eq367 (τ X0)
       grind)
    | exact superpose eq367 eq132642
    | (have j0 := eq132642 X0 X1 X2
       grind)
    | exact resolve eq132642 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367 eq132642
  have eq132999 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (k (σ X2) X0) = (M.op (σ X2) X0) ∨ (σ X2) = (M.op X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq132874 X0 X1 X2
       have i₂ := eq19 X0 X2
       grind)
    | exact superpose eq19 eq132874
    | (have j0 := eq132874 X0 X1 X2
       grind)
    | exact resolve eq132874 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq132874
  have eq155088 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq868 X0
       have i₂ := eq132999 (σ X0) (σ X0) x
       grind)
    | exact superpose eq132999 eq868
    | (have j1 := eq132999 (σ X0) X1 X1
       grind)
    | exact resolve eq868 eq132999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868 eq132999
  have eq155206 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq155088 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq155088
    | (have j0 := eq155088 X0 X1
       grind)
    | exact resolve eq155088 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155088
  have eq155371 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq155206 X0 X1
       have i₂ := eq29726 X0
       grind)
    | exact superpose eq29726 eq155206
    | (have j0 := eq155206 X0 X1
       grind)
    | exact resolve eq155206 eq29726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29726 eq155206
  have eq155499 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq155371 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq155371
    | (have j0 := eq155371 X0 X1
       grind)
    | exact resolve eq155371 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155371
  have eq155563 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq155499 X0 X1
       have i₂ := eq30535 X0
       grind)
    | exact superpose eq30535 eq155499
    | (have j0 := eq155499 X0 X1
       grind)
    | exact resolve eq155499 eq30535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30535 eq155499
  have eq982852 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq155563 y x
       grind)
    | exact superpose eq155563 eq16
    | (have j1 := eq155563 y x
       grind)
    | exact resolve eq16 eq155563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155563
  have eq984457 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq982852
       have i₂ := eq697 x y
       grind)
    | exact superpose eq697 eq982852
    | (have j1 := eq697 y y
       grind)
    | (have r₁ := eq982852
       have r₂ := eq697 x y
       grind)
    | exact resolve eq982852 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697 eq982852
  have eq984458 : y = (M.op y x) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq984457
  have eq1352769 : y = (k y y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq62 y x
       have i₂ := eq984458
       grind)
    | exact superpose eq984458 eq62
    | exact resolve eq62 eq984458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq984458
  have eq1352983 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have j1 := eq557 y
       grind)
    | (have r₁ := eq1352769
       have r₂ := eq557 y
       grind)
    | exact resolve eq1352769 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557 eq1352769
  have eq1354088 : ∀ X0 : G, x = (M.op y y) ∨ y = (M.op X0 y) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq35 y y x
       have i₂ := eq1352983
       grind)
    | exact superpose eq1352983 eq35
    | exact resolve eq35 eq1352983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1352983
  have eq1355349 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op X0 y) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq32193 y
       have i₂ := eq1354088 X0
       grind)
    | exact superpose eq1354088 eq32193
    | (have j1 := eq1354088 X0
       grind)
    | exact resolve eq32193 eq1354088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1355381 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op X0 y) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq39 y y
       have i₂ := eq1354088 X0
       grind)
    | exact superpose eq1354088 eq39
    | (have j1 := eq1354088 X0
       grind)
    | exact resolve eq39 eq1354088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1354088
  have eq1379043 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op X0 y) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1355349 X0
       grind)
    | exact superpose eq1355349 eq16
    | (have j1 := eq1355349 X0
       grind)
    | exact resolve eq16 eq1355349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1355349
  have eq1381368 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ y = (M.op X0 y) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op X1 y) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1379043 X0
       have i₂ := eq1355381 X1
       grind)
    | exact superpose eq1355381 eq1379043
    | (have j0 := eq1379043 X0
       have j1 := eq1355381 X0
       grind)
    | exact resolve eq1379043 eq1355381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1355381 eq1379043
  have eq1381410 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ y = (M.op X0 y) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have j0 := eq1381368 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381368
  have eq1381411 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have j0 := eq1381410 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381410
  have eq1381812 : ∀ X0 : G, y ≠ y ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1381411 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381411
  have eq1381813 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq1381812 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381812
  have eq1384525 : ∀ X1 : G, (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op X1 (σ y)) := by
    intro X1
    first
    | (have i₁ := eq635 x y x
       have i₂ := eq1381813 x
       grind)
    | exact superpose eq1381813 eq635
    | exact resolve eq635 eq1381813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1384675 : ∀ X0 X1 : G, (σ x) = (σ (M.op y y)) ∨ (M.op X0 y) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 y X1
       have i₂ := eq1381813 (M.op y X0)
       grind)
    | exact superpose eq1381813 eq9
    | exact resolve eq9 eq1381813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1385038 : ∀ X0 : G, (M.op y y) = (τ (σ x)) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1384525 X0
       grind)
    | exact superpose eq1384525 eq10
    | (have j1 := eq1384525 X0
       grind)
    | exact resolve eq10 eq1384525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384525
  have eq1385828 : ∀ X0 : G, x = (M.op y y) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1385038 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1385038
    | (have j0 := eq1385038 X0
       grind)
    | exact resolve eq1385038 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1385038
  have eq1388036 : ∀ X0 X1 : G, x = (M.op X0 x) ∨ (σ y) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 y y x
       have i₂ := eq1385828 X0
       grind)
    | exact superpose eq1385828 eq35
    | (have j1 := eq1385828 X1
       grind)
    | exact resolve eq35 eq1385828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1385828
  have eq1391209 : ∀ X0 X1 X2 : G, (σ y) = (M.op X2 (σ y)) ∨ (M.op X0 x) = (M.op X1 x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 x X1
       have i₂ := eq1388036 (M.op x X0) X2
       grind)
    | exact superpose eq1388036 eq9
    | (have j1 := eq1388036 X0 X2
       grind)
    | exact resolve eq9 eq1388036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1388036
  have eq1402314 : ∀ X0 X1 : G, (M.op y y) = (τ (σ x)) ∨ (M.op X0 y) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1384675 X0 X1
       grind)
    | exact superpose eq1384675 eq10
    | (have j1 := eq1384675 X0 X1
       grind)
    | exact resolve eq10 eq1384675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384675
  have eq1403108 : ∀ X0 X1 : G, x = (M.op y y) ∨ (M.op X0 y) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq1402314 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1402314
    | (have j0 := eq1402314 X0 X1
       grind)
    | exact resolve eq1402314 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402314
  have eq1404688 : ∀ X0 X1 : G, x = (M.op x y) ∨ (M.op X0 y) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq39 y y
       have i₂ := eq1403108 X0 X1
       grind)
    | exact superpose eq1403108 eq39
    | (have j1 := eq1403108 X0 X1
       grind)
    | exact resolve eq39 eq1403108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1404829 : ∀ X0 : G, x ≠ (M.op X0 y) ∨ (M.op y y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1403108 y X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1403108
  have eq1431610 : ∀ X1 X2 X3 : G, (τ (σ y)) = (M.op X1 (τ (σ y))) ∨ (M.op X2 x) = (M.op X3 x) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq1481 X2 (σ y) X2
       have i₂ := eq1391209 x X1 X2
       grind)
    | exact superpose eq1391209 eq1481
    | (have j1 := eq1391209 X2 X3 X2
       grind)
    | exact resolve eq1481 eq1391209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1481
  have eq1431851 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op X0 x) = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq1391209 X0 X1 (σ x)
       grind)
    | exact superpose eq1391209 eq16
    | (have j1 := eq1391209 X0 X1 x
       grind)
    | exact resolve eq16 eq1391209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1391209
  have eq1432100 : ∀ X1 X2 X3 : G, y = (M.op X1 y) ∨ (M.op X2 x) = (M.op X3 x) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq1431610 X1 X2 X3
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1431610
    | (have j0 := eq1431610 X1 X2 X3
       grind)
    | exact resolve eq1431610 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1431610
  have eq1447553 : ∀ X0 X1 X2 X3 : G, (σ y) ≠ (σ y) ∨ (M.op X0 x) = (M.op X1 x) ∨ (M.op X2 x) = (M.op X3 x) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1431851 X0 X1
       have i₂ := eq1432100 x X2 X3
       grind)
    | exact superpose eq1432100 eq1431851
    | (have j0 := eq1431851 X0 X1
       have j1 := eq1432100 X1 X0 X1
       grind)
    | exact resolve eq1431851 eq1432100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1431851 eq1432100
  have eq1447600 : ∀ X0 X1 X2 X3 : G, (M.op X0 x) = (M.op X1 x) ∨ (M.op X2 x) = (M.op X3 x) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1447553 X0 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447553
  have eq1451917 : ∀ X0 X1 X2 : G, (M.op X1 x) ≠ (M.op X2 x) ∨ (M.op X0 x) = (M.op X2 x) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1447600 X0 X2 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1451918 : ∀ X0 X2 : G, (M.op X0 x) = (M.op X2 x) := by
    intro X0 X2
    first
    | (have j0 := eq1451917 X0 x X2
       have j1 := eq1447600 X0 X2 X0 X2
       grind)
    | (have r₁ := eq1451917 X0 X0 x
       have r₂ := eq1447600 X0 x X2 x
       grind)
    | (have r₁ := eq1451917 X0 x X0
       have r₂ := eq1447600 X0 x X2 x
       grind)
    | (have r₁ := eq1451917 X0 X2 x
       have r₂ := eq1447600 X0 x X2 x
       grind)
    | exact resolve eq1451917 eq1447600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447600 eq1451917
  have eq1455094 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op X0 x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1 x
       have i₂ := eq1451918 X1 X0
       grind)
    | (have i₁ := eq39 X1 x
       have i₂ := eq1451918 X0 X1
       grind)
    | exact superpose eq1451918 eq39
    | exact resolve eq39 eq1451918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq1451918
  have eq1460339 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq1404829 (M.op x x)
       have i₂ := eq1455094 x y
       grind)
    | exact superpose eq1455094 eq1404829
    | (have j0 := eq1404829 x
       grind)
    | exact resolve eq1404829 eq1455094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1404829 eq1455094
  have eq1460343 : (M.op x y) = (M.op y y) := by
    first
    | (have j1 := eq1404688 x y
       grind)
    | (have r₁ := eq1460339
       have r₂ := eq1404688 x x
       grind)
    | exact resolve eq1460339 eq1404688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1404688 eq1460339
  have eq1463376 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1381813 y
       have i₂ := eq1460343
       grind)
    | exact superpose eq1460343 eq1381813
    | (have j0 := eq1381813 x
       grind)
    | exact resolve eq1381813 eq1460343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381813
  have eq1463416 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq32193 y
       have i₂ := eq1460343
       grind)
    | exact superpose eq1460343 eq32193
    | exact resolve eq32193 eq1460343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32193 eq1460343
  have eq1474896 : ∀ X0 : G, (σ (M.op x y)) = (σ x) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq35 x y x
       have i₂ := eq1463376
       grind)
    | exact superpose eq1463376 eq35
    | exact resolve eq35 eq1463376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1463376
  have eq1482380 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq1463416
       have i₂ := eq1474896 X0
       grind)
    | exact superpose eq1474896 eq1463416
    | (have j1 := eq1474896 X0
       grind)
    | exact resolve eq1463416 eq1474896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1463416
  have eq1490646 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1482380 X0
       grind)
    | exact superpose eq1482380 eq16
    | (have j1 := eq1482380 X0
       grind)
    | exact resolve eq16 eq1482380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1482380
  have eq1490987 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1490646 X0
       have j1 := eq1474896 X0
       grind)
    | (have r₁ := eq1490646 X0
       have r₂ := eq1474896 X0
       grind)
    | exact resolve eq1490646 eq1474896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474896 eq1490646
  have eq1492887 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) := by
    intro X1
    first
    | (have i₁ := eq635 x y x
       have i₂ := eq1490987 x
       grind)
    | exact superpose eq1490987 eq635
    | exact resolve eq635 eq1490987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq1493862 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1492887 (σ x)
       grind)
    | exact superpose eq1492887 eq16
    | exact resolve eq16 eq1492887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1492887
  have eq1493996 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1493862
       have i₂ := eq1490987 x
       grind)
    | exact superpose eq1490987 eq1493862
    | exact resolve eq1493862 eq1490987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1490987 eq1493862
  have eq1493997 : False := by grind
  exact eq1493997

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation3600 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3600 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 X0) X1) X3
       have i₂ := eq9 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq20 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq25 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 x
       have i₂ := eq21 (M.op X0 X1) X0 x
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) X2) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 X1)
       have i₂ := eq21 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq21 eq12
    | (have j0 := eq12 X2 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X1)
       have r₂ := eq21 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq47 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq51 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq60 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq47
    | exact resolve eq47 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq82 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq53
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq101 : ∀ X0 X1 X2 : G, (k X2 (τ (M.op X0 X1))) = (τ (M.op (M.op X0 X1) (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X2 (M.op X0 X1)
       have i₂ := eq43 X0 X1 (σ X2)
       grind)
    | exact superpose eq43 eq53
    | exact resolve eq53 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq102 : ∀ X0 X1 X2 : G, (k X2 (σ (M.op X0 X1))) = (σ (M.op (M.op X0 X1) (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X2 (M.op X0 X1)
       have i₂ := eq43 X0 X1 (τ X2)
       grind)
    | exact superpose eq43 eq17
    | exact resolve eq17 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq212 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k X1 (τ (M.op (σ X1) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq101 (σ X1) X0 X1
       have i₂ := eq25 (σ X1) X0
       grind)
    | exact superpose eq25 eq101
    | exact resolve eq101 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq258 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq81 x y
       grind)
    | exact superpose eq81 eq16
    | (have j1 := eq81 x y
       grind)
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq81 X0 X0
       grind)
    | exact superpose eq81 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq81 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq81 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq81 X0 X1
       grind)
    | exact resolve eq12 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq81 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq271 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq270 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq272 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq268 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq274 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq272 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq272 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq272 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq293 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (k X1 (σ (M.op (τ X1) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq102 (τ X1) X0 X1
       have i₂ := eq25 (τ X1) X0
       grind)
    | exact superpose eq25 eq102
    | exact resolve eq102 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq490 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op (M.op X0 X1) (M.op X0 X1))) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq271 (M.op X0 X1)
       have i₂ := eq43 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq43 eq271
    | (have j0 := eq271 (M.op X0 X1)
       grind)
    | exact resolve eq271 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq499 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq490 X0 X1
       have i₂ := eq21 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq21 eq490
    | (have j0 := eq490 X0 X1
       grind)
    | exact resolve eq490 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq500 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq499 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq511 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) ≠ (σ (M.op (M.op X0 X1) (M.op X0 X1))) ∨ (k X2 (σ (M.op X0 X1))) = (M.op (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq274 (M.op X0 X1) X2
       have i₂ := eq43 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq43 eq274
    | (have j0 := eq274 (M.op X0 X1) X2
       grind)
    | exact resolve eq274 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (k X2 (σ (M.op X0 X1))) = (M.op (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq511 X0 X1 X2
       have i₂ := eq21 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq21 eq511
    | (have j0 := eq511 X0 X1 X2
       grind)
    | exact resolve eq511 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq521 : ∀ X0 X1 X2 : G, (k X2 (σ (M.op X0 X1))) = (M.op (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq520 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq542 : ∀ X0 X1 : G, (σ (M.op X1 (τ X0))) = (M.op (σ (M.op (τ X0) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq293 X1 X0
       have i₂ := eq521 (τ X0) X1 X0
       grind)
    | exact superpose eq521 eq293
    | exact resolve eq293 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293 eq521
  have eq617 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (σ (M.op X0 (τ (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X1 X2 (σ (M.op (τ (M.op X1 X2)) X0))
       have i₂ := eq542 (M.op X1 X2) X0
       grind)
    | exact superpose eq542 eq21
    | exact resolve eq21 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (σ (M.op (τ (M.op X0 X1)) (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq542 X2 (τ (M.op X0 X1))
       have i₂ := eq617 (τ X2) X0 X1
       grind)
    | exact superpose eq617 eq542
    | exact resolve eq542 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X2 (τ (M.op X0 X1)))
       have i₂ := eq617 X2 X0 X1
       grind)
    | exact superpose eq617 eq10
    | exact resolve eq10 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq791 : ∀ X0 X1 X3 : G, (M.op (τ (M.op X0 X1)) X3) = (k X3 (τ (M.op X0 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq43 x (τ (M.op X0 X1)) x
       have i₂ := eq661 X0 X1 x
       grind)
    | exact superpose eq661 eq43
    | exact resolve eq43 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq1040 : ∀ X0 X1 X2 : G, (τ X2) = (M.op (τ X2) (τ X2)) ∨ (M.op X0 X1) = (τ X2) ∨ (σ (M.op X0 X1)) = (k (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq84 X0 (M.op X0 X1)
       have i₂ := eq21 X0 X1 (τ X0)
       grind)
    | exact superpose eq21 eq84
    | (have j0 := eq84 X2 (τ X2)
       grind)
    | exact resolve eq84 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq1277 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq258
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq258
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq258 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1278 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq1277
  have eq1294 : ∀ X0 X1 : G, (τ (M.op X1 (σ X0))) = (M.op (τ (M.op (σ X0) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq212 X1 X0
       have i₂ := eq791 (σ X0) X1 X0
       grind)
    | exact superpose eq791 eq212
    | exact resolve eq212 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq13884 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq82 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq13885 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq13884 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13884
  have eq13888 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq13885 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13885
    | (have j0 := eq13885 X0
       grind)
    | exact resolve eq13885 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13885
  have eq15031 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13888 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13888
    | exact resolve eq13888 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13888
  have eq15158 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15031 X0
       have i₂ := eq60 X0 X0
       grind)
    | exact superpose eq60 eq15031
    | (have j0 := eq15031 X0
       grind)
    | exact resolve eq15031 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15031
  have eq15232 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq15158 X0
       grind)
    | exact superpose eq15158 eq11
    | (have j1 := eq15158 X0
       grind)
    | exact resolve eq11 eq15158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15158
  have eq15329 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15232 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq15232
    | (have j0 := eq15232 X0
       grind)
    | exact resolve eq15232 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15232
  have eq15367 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq15329 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq15329 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq15329 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15329
  have eq15397 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq274 X0 X1
       have i₂ := eq15367 X0
       grind)
    | exact superpose eq15367 eq274
    | (have j0 := eq274 X0 X1
       grind)
    | exact resolve eq274 eq15367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq15407 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq269 X0 X0
       have i₂ := eq15367 X0
       grind)
    | exact superpose eq15367 eq269
    | (have j0 := eq269 X0 X0
       grind)
    | exact resolve eq269 eq15367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq15436 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq15367 (σ X0)
       grind)
    | exact superpose eq15367 eq15
    | exact resolve eq15 eq15367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15443 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq60 X0 X0
       have i₂ := eq15367 (τ X0)
       grind)
    | exact superpose eq15367 eq60
    | exact resolve eq60 eq15367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15470 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq15407 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15407
  have eq15497 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15443 X0
       have i₂ := eq15367 X0
       grind)
    | exact superpose eq15367 eq15443
    | exact resolve eq15443 eq15367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15443
  have eq15503 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15436 X0
       have i₂ := eq15367 X0
       grind)
    | exact superpose eq15367 eq15436
    | exact resolve eq15436 eq15367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15436
  have eq19004 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have j0 := eq1040 (τ X0) (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040
  have eq19005 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have j0 := eq19004 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19004
  have eq19011 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq19005 X0
       have i₂ := eq15497 X0
       grind)
    | exact superpose eq15497 eq19005
    | (have j0 := eq19005 X0
       grind)
    | exact resolve eq19005 eq15497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19005
  have eq19062 : ∀ X0 : G, (σ (τ (M.op X0 X0))) = (k (σ (τ (M.op X0 X0))) X0) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq19011 X0
       have i₂ := eq15497 X0
       grind)
    | exact superpose eq15497 eq19011
    | (have j0 := eq19011 X0
       grind)
    | exact resolve eq19011 eq15497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19011
  have eq19072 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq19062 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq19062
    | (have j0 := eq19062 X0
       grind)
    | exact resolve eq19062 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19062
  have eq19115 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq47 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq19072 (σ X0)
       grind)
    | exact superpose eq19072 eq47
    | (have j1 := eq19072 (σ X0)
       grind)
    | exact resolve eq47 eq19072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19072
  have eq19171 : ∀ X0 : G, (τ (σ (M.op X0 X0))) = (k (τ (σ (M.op X0 X0))) X0) ∨ (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq19115 X0
       have i₂ := eq15503 X0
       grind)
    | exact superpose eq15503 eq19115
    | (have j0 := eq19115 X0
       grind)
    | exact resolve eq19115 eq15503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19115
  have eq19208 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq19171 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq19171
    | (have j0 := eq19171 X0
       grind)
    | exact resolve eq19171 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19171
  have eq19235 : ∀ X0 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq19208 X0
       have i₂ := eq15503 X0
       grind)
    | exact superpose eq15503 eq19208
    | (have j0 := eq19208 X0
       grind)
    | exact resolve eq19208 eq15503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19208
  have eq19254 : ∀ X0 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq19235 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq19235
    | (have j0 := eq19235 X0
       grind)
    | exact resolve eq19235 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19235
  have eq19271 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq19254 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19254
    | (have j0 := eq19254 X0
       grind)
    | exact resolve eq19254 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19254
  have eq19324 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq19271 (σ X0)
       grind)
    | exact superpose eq19271 eq47
    | (have j1 := eq19271 (σ X0)
       grind)
    | exact resolve eq47 eq19271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq19271
  have eq19384 : ∀ X0 : G, (τ (σ (M.op X0 X0))) = (k (τ (σ (M.op X0 X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq19324 X0
       have i₂ := eq15503 X0
       grind)
    | exact superpose eq15503 eq19324
    | (have j0 := eq19324 X0
       grind)
    | exact resolve eq19324 eq15503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19324
  have eq19413 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq19384 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq19384
    | (have j0 := eq19384 X0
       grind)
    | exact resolve eq19384 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19384
  have eq19436 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq19413 X0
       have i₂ := eq15503 X0
       grind)
    | exact superpose eq15503 eq19413
    | (have j0 := eq19413 X0
       grind)
    | exact resolve eq19413 eq15503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19413
  have eq19833 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 X0)) (τ X0)) ∨ (σ (τ X0)) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq19436 (τ X0)
       have i₂ := eq15497 X0
       grind)
    | exact superpose eq15497 eq19436
    | exact resolve eq19436 eq15497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15497 eq19436
  have eq19921 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (k (M.op X0 X0) X0)) ∨ (σ (τ X0)) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq19833 X0
       have i₂ := eq60 X0 (M.op X0 X0)
       grind)
    | exact superpose eq60 eq19833
    | (have j0 := eq19833 X0
       grind)
    | exact resolve eq19833 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq19833
  have eq19955 : ∀ X0 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (τ (M.op X0 X0)) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq19921 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq19921
    | (have j0 := eq19921 X0
       grind)
    | exact resolve eq19921 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19921
  have eq19981 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (k (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq19955 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19955
    | (have j0 := eq19955 X0
       grind)
    | exact resolve eq19955 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19955
  have eq20818 : ∀ X0 X1 X2 : G, (σ (M.op (τ (M.op X1 X2)) (τ (M.op X0 X0)))) = (M.op (M.op X1 X2) (k (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq658 X1 X2 (k (M.op X0 X0) X0)
       have i₂ := eq19981 X0
       grind)
    | exact superpose eq19981 eq658
    | (have j1 := eq19981 X0
       grind)
    | exact resolve eq658 eq19981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq19981
  have eq20840 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X2) (k (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20818 X0 X1 X2
       have i₂ := eq617 (τ (M.op X1 X2)) X0 X0
       grind)
    | exact superpose eq617 eq20818
    | (have j0 := eq20818 X0 X1 X2
       grind)
    | exact resolve eq20818 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617 eq20818
  have eq24870 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq500 x y
       have i₂ := eq1278
       grind)
    | exact superpose eq1278 eq500
    | exact resolve eq500 eq1278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500 eq1278
  have eq24917 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq24870
  have eq24966 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq24917
       have i₂ := eq15503 x
       grind)
    | exact superpose eq15503 eq24917
    | exact resolve eq24917 eq15503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24917
  have eq33991 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (k (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25 (k (M.op X0 X0) X0) X1
       have i₂ := eq20840 X0 (k (M.op X0 X0) X0) X1
       grind)
    | exact superpose eq20840 eq25
    | (have j1 := eq20840 X0 X1 x
       grind)
    | exact resolve eq25 eq20840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20840
  have eq34277 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (τ (M.op X1 (σ (k (M.op X0 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1294 (k (M.op X0 X0) X0) X1
       have i₂ := eq33991 X0 (τ (M.op (σ (k (M.op X0 X0) X0)) X1))
       grind)
    | exact superpose eq33991 eq1294
    | (have j1 := eq33991 X0 X1
       grind)
    | exact resolve eq1294 eq33991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294 eq33991
  have eq37254 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (τ (M.op X2 (σ (k (M.op X0 X0) X0)))) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X0 X0 x
       have i₂ := eq34277 X0 X1
       grind)
    | exact superpose eq34277 eq21
    | (have j1 := eq34277 X0 X2
       grind)
    | exact resolve eq21 eq34277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34277
  have eq39361 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (τ (σ (M.op X0 (τ (σ (k (M.op X1 X1) X1)))))) ∨ (M.op X2 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq37254 X1 X2 (σ (M.op (τ (σ (k (M.op X1 X1) X1))) X0))
       have i₂ := eq542 (σ (k (M.op X1 X1) X1)) X0
       grind)
    | exact superpose eq542 eq37254
    | (have j0 := eq37254 X1 X2 X2
       grind)
    | exact resolve eq37254 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542 eq37254
  have eq39585 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X0 (τ (σ (k (M.op X1 X1) X1)))) ∨ (M.op X2 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39361 X0 X1 X2
       have i₂ := eq10 (M.op X0 (τ (σ (k (M.op X1 X1) X1))))
       grind)
    | exact superpose eq10 eq39361
    | (have j0 := eq39361 X0 X1 X2
       grind)
    | exact resolve eq39361 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39361
  have eq39673 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X0 (k (M.op X1 X1) X1)) ∨ (M.op X2 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39585 X0 X1 X2
       have i₂ := eq10 (k (M.op X1 X1) X1)
       grind)
    | exact superpose eq10 eq39585
    | (have j0 := eq39585 X0 X1 X2
       grind)
    | exact resolve eq39585 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39585
  have eq39874 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (k (M.op X0 X0) X0) X1) ∨ (M.op X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X1 (k (M.op X0 X0) X0)
       have i₂ := eq39673 X1 X0 X2
       grind)
    | exact superpose eq39673 eq25
    | (have j1 := eq39673 X0 X0 X2
       grind)
    | exact resolve eq25 eq39673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39673
  have eq46566 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ X0 ∨ (M.op (k (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq39874 X0 x (k (M.op X0 X0) X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39874
  have eq46570 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op (k (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq46566 X0
       have i₂ := eq25 X0 X0
       grind)
    | exact superpose eq25 eq46566
    | (have j0 := eq46566 X0
       grind)
    | exact resolve eq46566 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46566
  have eq95369 : ∀ X0 : G, (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq791 (σ x) (σ y) x
       have i₂ := eq24966
       grind)
    | exact superpose eq24966 eq791
    | exact resolve eq791 eq24966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24966
  have eq95473 : ∀ X0 : G, (M.op x X0) = (k X0 x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq95369 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq95369
    | exact resolve eq95369 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95369
  have eq95504 : ∀ X0 : G, (M.op x X0) = (k X0 x) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq95473 X0
       have j1 := eq12 X0 x
       grind)
    | (have r₁ := eq95473 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq95473 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95473
  have eq97632 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq258
       have i₂ := eq95504 y
       grind)
    | exact superpose eq95504 eq258
    | exact resolve eq258 eq95504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258 eq95504
  have eq97633 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq97632
  have eq97638 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq15470 x
       grind)
    | (have r₁ := eq97633
       have r₂ := eq15470 x
       grind)
    | exact resolve eq97633 eq15470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15470 eq97633
  have eq97697 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq97638
       have i₂ := eq15503 x
       grind)
    | exact superpose eq15503 eq97638
    | exact resolve eq97638 eq15503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97638
  have eq99449 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq21 (σ x) (σ y) x
       have i₂ := eq97697
       grind)
    | exact superpose eq97697 eq21
    | exact resolve eq21 eq97697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq99451 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq43 (σ x) (σ y) x
       have i₂ := eq97697
       grind)
    | exact superpose eq97697 eq43
    | exact resolve eq43 eq97697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97697
  have eq99605 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq99451 X0
       have j1 := eq15397 x X0
       grind)
    | (have r₁ := eq99451 X0
       have r₂ := eq15397 x x
       grind)
    | exact resolve eq99451 eq15397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15397 eq99451
  have eq99725 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq99605 (σ X0)
       grind)
    | exact superpose eq99605 eq15
    | exact resolve eq15 eq99605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99726 : ∀ X0 X1 : G, (σ (k X1 (k X0 (τ (σ x))))) = (k (σ X1) (M.op (σ x) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 (σ x) X1
       have i₂ := eq99605 (σ X0)
       grind)
    | exact superpose eq99605 eq51
    | exact resolve eq51 eq99605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq99605
  have eq99818 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ X0)) (σ X1)) = (σ (k X1 (k X0 (τ (σ x))))) := by
    intro X0 X1
    first
    | (have i₁ := eq99726 X0 X1
       have i₂ := eq43 (σ x) (σ X0) (σ X1)
       grind)
    | exact superpose eq43 eq99726
    | exact resolve eq99726 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99726
  have eq99895 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ X0)) (σ X1)) = (σ (k X1 (k X0 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq99818 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq99818
    | exact resolve eq99818 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99818
  have eq99938 : ∀ X0 X1 : G, (σ (k X1 (k X0 x))) = (M.op (σ (k X0 x)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq99895 X0 X1
       have i₂ := eq99725 X0
       grind)
    | exact superpose eq99725 eq99895
    | exact resolve eq99895 eq99725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99895
  have eq101613 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq99725 y
       grind)
    | exact superpose eq99725 eq16
    | exact resolve eq16 eq99725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101701 : (σ x) ≠ (σ (k x x)) ∨ (σ x) = (M.op (k (σ (k x x)) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq46570 (σ x)
       have i₂ := eq99725 x
       grind)
    | exact superpose eq99725 eq46570
    | exact resolve eq46570 eq99725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46570
  have eq101709 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (M.op (σ (k X0 x)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq25 (σ x) (σ X0)
       have i₂ := eq99725 X0
       grind)
    | exact superpose eq99725 eq25
    | exact resolve eq25 eq99725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq101742 : ∀ X0 X1 : G, (k X1 (τ (σ (k X0 x)))) = (M.op (τ (σ (k X0 x))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq791 (σ x) (σ X0) x
       have i₂ := eq99725 X0
       grind)
    | exact superpose eq99725 eq791
    | exact resolve eq791 eq99725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791 eq99725
  have eq101848 : ∀ X0 X1 : G, (k X1 (k X0 x)) = (M.op (k X0 x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq101742 X0 X1
       have i₂ := eq10 (k X0 x)
       grind)
    | exact superpose eq10 eq101742
    | exact resolve eq101742 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101742
  have eq101868 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (k x (k X0 x))) := by
    intro X0
    first
    | (have i₁ := eq101709 X0
       have i₂ := eq99938 X0 x
       grind)
    | exact superpose eq99938 eq101709
    | exact resolve eq101709 eq99938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101709
  have eq101875 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (k (σ (k x x)) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq101701
       have i₂ := eq15367 x
       grind)
    | exact superpose eq15367 eq101701
    | exact resolve eq101701 eq15367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15367 eq101701
  have eq102043 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (M.op (k X0 x) x)) := by
    intro X0
    first
    | (have i₁ := eq101868 X0
       have i₂ := eq101848 X0 x
       grind)
    | exact superpose eq101848 eq101868
    | exact resolve eq101868 eq101848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101868
  have eq102049 : (σ x) = (M.op (k (σ (k x x)) (σ x)) (σ x)) := by
    first
    | (have j1 := eq99449 (k (σ (k x x)) (σ x))
       grind)
    | (have r₁ := eq101875
       have r₂ := eq99449 x
       grind)
    | exact resolve eq101875 eq99449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99449 eq101875
  have eq102148 : (σ x) = (M.op (σ (k (k x x) x)) (σ x)) := by
    first
    | (have i₁ := eq102049
       have i₂ := eq15 (k x x) x
       grind)
    | exact superpose eq15 eq102049
    | exact resolve eq102049 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102049
  have eq102197 : (σ x) = (σ (k x (k (k x x) x))) := by
    first
    | (have i₁ := eq102148
       have i₂ := eq99938 (k x x) x
       grind)
    | exact superpose eq99938 eq102148
    | exact resolve eq102148 eq99938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102148
  have eq102221 : (σ x) = (σ (M.op (k (k x x) x) x)) := by
    first
    | (have i₁ := eq102197
       have i₂ := eq101848 (k x x) x
       grind)
    | exact superpose eq101848 eq102197
    | exact resolve eq102197 eq101848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102197
  have eq102232 : (σ x) = (M.op (σ (k x x)) (σ x)) := by
    first
    | (have i₁ := eq102221
       have i₂ := eq102043 (k x x)
       grind)
    | exact superpose eq102043 eq102221
    | exact resolve eq102221 eq102043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102221
  have eq102237 : (σ x) = (σ (k x (k x x))) := by
    first
    | (have i₁ := eq102232
       have i₂ := eq99938 x x
       grind)
    | exact superpose eq99938 eq102232
    | exact resolve eq102232 eq99938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99938 eq102232
  have eq102241 : (σ x) = (σ (M.op (k x x) x)) := by
    first
    | (have i₁ := eq102237
       have i₂ := eq101848 x x
       grind)
    | exact superpose eq101848 eq102237
    | exact resolve eq102237 eq101848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101848 eq102237
  have eq102245 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq102241
       have i₂ := eq102043 x
       grind)
    | exact superpose eq102043 eq102241
    | exact resolve eq102241 eq102043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102043 eq102241
  have eq102248 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq102245
       have i₂ := eq15503 x
       grind)
    | exact superpose eq15503 eq102245
    | exact resolve eq102245 eq15503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15503 eq102245
  have eq102284 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq102248
       grind)
    | exact superpose eq102248 eq10
    | exact resolve eq10 eq102248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102248
  have eq102482 : x = (M.op x x) := by
    first
    | (have i₁ := eq102284
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq102284
    | exact resolve eq102284 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102284
  have eq102962 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq43 x x x
       have i₂ := eq102482
       grind)
    | exact superpose eq102482 eq43
    | exact resolve eq43 eq102482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq102482
  have eq106955 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq101613
       have i₂ := eq102962 y
       grind)
    | exact superpose eq102962 eq101613
    | exact resolve eq101613 eq102962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101613 eq102962
  have eq106966 : False := by grind
  exact eq106966

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxy_pxx_pyx_Equation3600 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3600 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  have eq109 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 X0) X1) X3
       have i₂ := eq9 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq109 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq109
    | exact resolve eq109 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq111 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq110 (σ X0) (σ X0) x
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq110
    | exact resolve eq110 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq110 (τ X0) (τ X0) x
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq110
    | exact resolve eq110 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq135 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq111 (M.op X0 X1) X1
       have i₂ := eq110 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq110 eq111
    | exact resolve eq111 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq168 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq112 (M.op X0 X1) X1
       have i₂ := eq110 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq110 eq112
    | exact resolve eq112 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq720 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq722 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq1074 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq722 x y
       grind)
    | exact superpose eq722 eq16
    | (have j1 := eq722 x y
       grind)
    | exact resolve eq16 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq11567 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq720 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq720
    | exact resolve eq720 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq11659 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11567 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq11567
    | (have j0 := eq11567 X0 X1
       grind)
    | exact resolve eq11567 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11567
  have eq35844 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1074
       have i₂ := eq11659 x y
       grind)
    | exact superpose eq11659 eq1074
    | (have j1 := eq11659 (σ x) (σ y)
       grind)
    | (have r₁ := eq1074
       have r₂ := eq11659 x y
       grind)
    | (have r₁ := eq1074
       have r₂ := eq11659 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1074
       have r₂ := eq11659 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1074 eq11659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074 eq11659
  have eq35845 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq35844
  have eq85771 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35845
       grind)
    | exact superpose eq35845 eq16
    | exact resolve eq16 eq35845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35845
  have eq85780 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq85771
       have r₂ := eq22 x
       grind)
    | exact resolve eq85771 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85771
  have eq86489 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq85780
       grind)
    | exact superpose eq85780 eq10
    | exact resolve eq10 eq85780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85780
  have eq86594 : x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq86489
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq86489
    | exact resolve eq86489 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86489
  have eq86599 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq86594
       grind)
    | exact superpose eq86594 eq16
    | exact resolve eq16 eq86594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86594
  have eq86608 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq86599
       have r₂ := eq22 x
       grind)
    | exact resolve eq86599 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq86599
  have eq86622 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq110 x y x
       have i₂ := eq86608
       grind)
    | exact superpose eq86608 eq110
    | exact resolve eq110 eq86608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq86608
  have eq86724 : ∀ X0 X1 : G, (τ (σ y)) = (M.op X0 (τ (σ y))) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq168 (σ x) (σ y) x
       have i₂ := eq86622 X0
       grind)
    | exact superpose eq86622 eq168
    | (have j1 := eq86622 X1
       grind)
    | exact resolve eq168 eq86622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq86622
  have eq86844 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq86724 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq86724
    | (have j0 := eq86724 X0 X0
       grind)
    | exact resolve eq86724 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86724
  have eq87087 : ∀ X0 : G, y ≠ y ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq86844 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86844
  have eq87088 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq87087 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87087
  have eq87213 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) := by
    intro X1
    first
    | (have i₁ := eq135 x y x
       have i₂ := eq87088 x
       grind)
    | exact superpose eq87088 eq135
    | exact resolve eq135 eq87088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq87556 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq87213 (σ x)
       grind)
    | exact superpose eq87213 eq16
    | exact resolve eq16 eq87213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87213
  have eq87561 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq87556
       have i₂ := eq87088 x
       grind)
    | exact superpose eq87088 eq87556
    | exact resolve eq87556 eq87088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87088 eq87556
  have eq87562 : False := by grind
  exact eq87562

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation3600 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3600 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) ≠ X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq109 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 X0) X1) X3
       have i₂ := eq9 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq109 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq109
    | exact resolve eq109 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq112 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq110 (τ X0) (τ X0) x
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq110
    | exact resolve eq110 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq168 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq112 (M.op X0 X1) X1
       have i₂ := eq110 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq110 eq112
    | exact resolve eq112 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq112
  have eq298 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq13 (σ X1) (σ X0)
       grind)
    | exact superpose eq13 eq15
    | (have j1 := eq13 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq668 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq670 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
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
  have eq3510 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq668 x y
       grind)
    | exact superpose eq668 eq16
    | (have j1 := eq668 x y
       grind)
    | exact resolve eq16 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3536 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq668 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq14321 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq670 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq670
    | exact resolve eq670 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq14462 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14321 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14321
    | (have j0 := eq14321 X0 X1
       grind)
    | exact resolve eq14321 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14321
  have eq14715 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) ≠ X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3536 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq3536
    | (have j0 := eq3536 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq3536 X0 X1
       have r₂ := eq13 (σ X0) (σ (k X1 X0))
       grind)
    | (have r₁ := eq3536 X0 X1
       have r₂ := eq13 (σ (k X1 X0)) (σ X0)
       grind)
    | (have r₁ := eq3536 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | exact resolve eq3536 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3536
  have eq14808 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) ≠ X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14715 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14715
  have eq26576 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3510
       have i₂ := eq14462 y x
       grind)
    | exact superpose eq14462 eq3510
    | (have j1 := eq14462 (σ y) (σ x)
       grind)
    | (have r₁ := eq3510
       have r₂ := eq14462 y x
       grind)
    | (have r₁ := eq3510
       have r₂ := eq14462 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq3510
       have r₂ := eq14462 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq3510 eq14462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3510
  have eq26577 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq26576
  have eq26579 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq14808 x y
       grind)
    | (have r₁ := eq26577
       have r₂ := eq14808 (σ x) (σ y)
       grind)
    | (have r₁ := eq26577
       have r₂ := eq14808 x y
       grind)
    | exact resolve eq26577 eq14808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14808 eq26577
  have eq26582 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26579
       grind)
    | exact superpose eq26579 eq16
    | exact resolve eq16 eq26579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26579
  have eq26583 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq26582
       have r₂ := eq22 x
       grind)
    | exact resolve eq26582 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26582
  have eq26585 : y = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq26583
       grind)
    | exact superpose eq26583 eq10
    | exact resolve eq10 eq26583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26583
  have eq26652 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26585
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq26585
    | exact resolve eq26585 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26585
  have eq26654 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26652
       grind)
    | exact superpose eq26652 eq16
    | exact resolve eq16 eq26652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26652
  have eq26655 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq26654
       have r₂ := eq22 x
       grind)
    | exact resolve eq26654 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq26654
  have eq26660 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26655
       grind)
    | exact superpose eq26655 eq16
    | exact resolve eq16 eq26655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26661 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq298 x y
       have i₂ := eq26655
       grind)
    | exact superpose eq26655 eq298
    | (have j0 := eq298 x y
       grind)
    | (have r₁ := eq298 x y
       have r₂ := eq26655
       grind)
    | exact resolve eq298 eq26655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq26671 : ∀ X0 : G, (τ (σ x)) = (M.op X0 (τ (σ x))) := by
    intro X0
    first
    | (have i₁ := eq168 (σ x) (σ y) x
       have i₂ := eq26655
       grind)
    | exact superpose eq26655 eq168
    | exact resolve eq168 eq26655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq26655
  have eq26724 : (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq26661
  have eq26752 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq26671 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq26671
    | exact resolve eq26671 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26671
  have eq30215 : y = (τ (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq26724
       grind)
    | exact superpose eq26724 eq10
    | exact resolve eq10 eq26724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26724
  have eq30290 : x = y ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq30215
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq30215
    | exact resolve eq30215 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30215
  have eq30300 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq26660
       have i₂ := eq30290
       grind)
    | exact superpose eq30290 eq26660
    | exact resolve eq26660 eq30290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30290
  have eq30301 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq30300
       have i₂ := eq26752 x
       grind)
    | exact superpose eq26752 eq30300
    | exact resolve eq30300 eq26752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30300
  have eq30302 : (σ x) = (σ (k y x)) := by grind
  clear eq30301
  have eq30311 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq14462 y x
       have i₂ := eq30302
       grind)
    | exact superpose eq30302 eq14462
    | (have j0 := eq14462 y x
       grind)
    | exact resolve eq14462 eq30302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14462 eq30302
  have eq30389 : x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq30311
       have r₂ := eq26660
       grind)
    | exact resolve eq30311 eq26660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30311
  have eq30418 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26660
       have i₂ := eq30389
       grind)
    | exact superpose eq30389 eq26660
    | exact resolve eq26660 eq30389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30389
  have eq30423 : (σ x) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30418
       have i₂ := eq26752 x
       grind)
    | exact superpose eq26752 eq30418
    | exact resolve eq30418 eq26752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26752 eq30418
  have eq30424 : x = (M.op x y) := by grind
  clear eq30423
  have eq30430 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq26660
       have i₂ := eq30424
       grind)
    | exact superpose eq30424 eq26660
    | exact resolve eq26660 eq30424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26660 eq30424
  have eq30489 : False := by grind
  exact eq30489

/-- `Equation3607`: `x ◇ y = z ◇ ((y ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_x_pxy_Equation3607 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3607 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3607.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X2) X0)) := by
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  have eq51 : ∀ X0 : G, (M.op X0 x) = (M.op y (M.op (M.op x y) X0)) := by
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
  have eq52 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X1 X3) X0) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3 (M.op (M.op X1 X3) X0)
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X2 X3)) X0) X2) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X1 (M.op X2 X3)) X0) X2 X3
       have i₂ := eq14 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq10
    | exact resolve eq10 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq44
    | exact resolve eq44 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq71 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq50
    | exact resolve eq50 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq72 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq71
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq71
    | exact resolve eq71 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq73 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq70
    | exact resolve eq70 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq69 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq69
    | exact resolve eq69 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq82 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq11 (M.op X0 X0) (k X1 X0)
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 (M.op X1 X0) (M.op X1 X1)
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X0
       have i₂ := eq11 X1 X0
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X2 X0
       have j1 := eq11 (M.op X0 X2) (k X2 X0)
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 (M.op X1 X0) (M.op X1 X1)
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq109 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq110 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq112 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq110
       have i₂ := eq67 sF3
       grind)
    | exact superpose eq67 eq110
    | exact resolve eq110 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq114 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq112
       have i₂ := eq67 y
       grind)
    | exact superpose eq67 eq112
    | exact resolve eq112 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq112
  have eq131 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq114
       grind)
    | exact superpose eq114 eq16
    | exact resolve eq16 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (M.op x y)) X0) x) = (M.op y (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op (M.op X1 sF0) X0)
       have i₂ := eq14 X0 X1 sF0
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op (M.op x y) X0) (M.op (M.op X0 x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op X0 (σ x)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq458 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X1 X3) X0)) = (M.op (M.op (M.op X0 X1) X4) (M.op (M.op X4 X3) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X4 X3 X2 (M.op (M.op X1 X3) X0)
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq460 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op (M.op (M.op X0 X1) X3) (M.op (M.op X3 X0) X2)) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X3 X0 X2 X0
       have i₂ := eq11 X1 X0
       grind)
    | (have i₁ := eq53 X0 X1 X2 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq53
    | (have j1 := eq11 (M.op X2 X0) (M.op (M.op (M.op X0 X1) X3) (M.op (M.op X3 X0) X2))
       grind)
    | exact resolve eq53 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq474 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op y X1) x) (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 x y X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 x y X0 X1
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (σ y) X1) (σ x)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) X0) X4) = (M.op (M.op (M.op X2 X4) (M.op X3 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X3 X1) X2 (M.op (M.op X2 X3) X0) X4
       have i₂ := eq53 X2 X3 X0 X1
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq484 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X1)) = (M.op (M.op (M.op X2 X3) X0) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X2 X3) X0) (M.op X3 X1) X2
       have i₂ := eq53 X2 X3 X0 X1
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq492 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq460 X0 X1 X2 x
       have i₂ := eq53 x X0 X2 X1
       grind)
    | exact superpose eq53 eq460
    | (have j0 := eq460 X0 X1 X2 x
       grind)
    | exact resolve eq460 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq597 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 (M.op X3 X0))) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op X2 (M.op X3 X0)) X1
       have i₂ := eq54 X1 X2 X3 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq858 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) ∨ (σ (k x X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq93
    | (have j0 := eq93 (σ (k x X0)) (M.op (σ x) (σ X0))
       grind)
    | exact resolve eq93 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq93
  have eq935 : ∀ X0 : G, (σ (k x X0)) = (σ (M.op X0 X0)) ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq858 X0
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq858
    | (have j0 := eq858 X0
       grind)
    | exact resolve eq858 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq858
  have eq1237 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq90 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq1694 : ∀ X0 X1 : G, (M.op x (M.op X1 (M.op x y))) = (M.op X0 (M.op y (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq226 eq14
    | exact resolve eq14 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq5170 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X2 (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq484 X1 X2 X0 (M.op X1 X0)
       have i₂ := eq53 X1 X0 X2 (M.op X1 X0)
       grind)
    | exact superpose eq53 eq484
    | exact resolve eq484 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5171 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op y (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq474 eq484
    | exact resolve eq484 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5172 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq476 eq484
    | exact resolve eq484 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq5293 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5170 X2 (M.op X1 X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq5170
    | exact resolve eq5170 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5305 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq51 eq5170
    | exact resolve eq5170 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5404 : ∀ X0 X1 : G, (M.op (M.op X1 X0) x) = (M.op y (M.op X0 (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 x)
       have i₂ := eq5170 sF0 X1 x
       grind)
    | (have i₁ := eq51 (M.op X1 X0)
       have i₂ := eq5170 X0 X1 sF0
       grind)
    | exact superpose eq5170 eq51
    | exact resolve eq51 eq5170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5527 : ∀ X0 : G, (M.op y X0) = (M.op (M.op (M.op y X0) x) x) := by
    intro X0
    first
    | exact superpose eq474 eq5305
    | exact resolve eq5305 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq5570 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) y) X0) = (M.op X1 (M.op (M.op X0 X1) x)) := by
    intro X0 X1
    first
    | exact superpose eq5305 eq14
    | exact resolve eq14 eq5305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5591 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | (have i₁ := eq5570 X0 x
       have i₂ := eq14 x X0 x
       grind)
    | exact superpose eq14 eq5570
    | exact resolve eq5570 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5570
  have eq5698 : ∀ X0 X1 : G, (M.op (M.op y X0) x) = (M.op X1 (M.op X0 (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq51 eq597
    | exact resolve eq597 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6803 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5293 (M.op (M.op X0 X1) X2) X2 X0
       have i₂ := eq53 X2 X0 X0 X1
       grind)
    | exact superpose eq53 eq5293
    | exact resolve eq5293 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq6847 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq232 x x
       have i₂ := eq5293 (M.op sF0 x) x x
       grind)
    | exact superpose eq5293 eq232
    | exact resolve eq232 eq5293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6848 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq241 x sF2
       have i₂ := eq5293 (M.op sF4 x) x sF2
       grind)
    | exact superpose eq5293 eq241
    | exact resolve eq241 eq5293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq6877 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (M.op (M.op (M.op (σ y) X2) (σ x)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq476 (M.op (M.op X1 X2) X2) X1
       have i₂ := eq5293 sF4 X1 X2
       grind)
    | exact superpose eq5293 eq476
    | exact resolve eq476 eq5293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6881 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op X0 X1) X1) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq476 eq6877
    | exact resolve eq6877 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476 eq6877
  have eq6903 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq27 eq6848
    | (have j0 := eq6848 X0
       grind)
    | exact resolve eq6848 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6848
  have eq6904 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq6847 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq6847
    | (have j0 := eq6847 X0
       grind)
    | exact resolve eq6847 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6847
  have eq7207 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6903 (M.op X1 x)
       have i₂ := eq5170 (M.op sF4 (M.op X1 x)) X1 x
       grind)
    | (have i₁ := eq6903 (M.op X1 X0)
       have i₂ := eq5170 X0 X1 (M.op sF4 (M.op X1 X0))
       grind)
    | exact superpose eq5170 eq6903
    | exact resolve eq6903 eq5170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6903
  have eq7334 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 (M.op (M.op x y) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6904 (M.op X1 x)
       have i₂ := eq5170 (M.op sF0 (M.op X1 x)) X1 x
       grind)
    | (have i₁ := eq6904 (M.op X1 X0)
       have i₂ := eq5170 X0 X1 (M.op sF0 (M.op X1 X0))
       grind)
    | exact superpose eq5170 eq6904
    | exact resolve eq6904 eq5170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6904
  have eq8004 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ y = X0 ∨ (M.op x y) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq492 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq492
    | (have j0 := eq492 X0 y x
       grind)
    | exact resolve eq492 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq10587 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X3 (M.op (M.op (M.op X2 (M.op X4 X1)) X5) X4)) = (M.op (M.op (M.op X0 (M.op X1 (M.op X0 X2))) X6) (M.op (M.op X6 X5) X3)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq458 X4 (M.op X2 (M.op X4 X1)) X3 X5 X6
       have i₂ := eq597 X1 X0 X2 X4
       grind)
    | (have i₁ := eq458 X4 (M.op X2 (M.op X4 X1)) X3 X5 X6
       have i₂ := eq597 X2 X4 X1 X0
       grind)
    | exact superpose eq597 eq458
    | exact resolve eq458 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq11017 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op (M.op X2 (M.op X4 X1)) X5) X4)) = (M.op X3 (M.op (M.op (M.op X1 (M.op X0 X2)) X5) X0)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq10587 X0 X1 X2 X3 X4 X5 x
       have i₂ := eq458 X0 (M.op X1 (M.op X0 X2)) X3 X5 x
       grind)
    | exact superpose eq458 eq10587
    | exact resolve eq10587 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458 eq10587
  have eq11065 : ∀ X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op (M.op X2 (M.op X4 X1)) X5) X4)) = (M.op X3 (M.op X2 (M.op X5 X1))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq11017 x X1 X2 X3 X4 X5
       have i₂ := eq54 X5 X1 x X2
       grind)
    | exact superpose eq54 eq11017
    | exact resolve eq11017 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11017
  have eq11071 : ∀ X1 X2 X3 X5 : G, (M.op X3 (M.op X2 (M.op X5 X1))) = (M.op X3 (M.op X1 (M.op X5 X2))) := by
    intro X1 X2 X3 X5
    first
    | (have i₁ := eq11065 X2 X1 X3 x X5
       have i₂ := eq54 X5 X1 x X2
       grind)
    | exact superpose eq54 eq11065
    | exact resolve eq11065 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq11065
  have eq12559 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) X0) X4) = (M.op X1 (M.op X0 (M.op (M.op X2 X4) (M.op X3 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq478 X0 X1 X2 X3 X4
       have i₂ := eq5170 (M.op (M.op X2 X4) (M.op X3 X1)) X0 X1
       grind)
    | (have i₁ := eq478 X0 X1 X2 X3 X4
       have i₂ := eq5170 X1 X0 (M.op (M.op X2 X4) (M.op X3 X1))
       grind)
    | exact superpose eq5170 eq478
    | exact resolve eq478 eq5170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq20899 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X0) (M.op (M.op x y) X2)) x) = (M.op X1 (M.op (M.op X0 X1) y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq232 eq12559
    | exact resolve eq12559 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12559
  have eq21203 : ∀ X0 X2 : G, (M.op y X0) = (M.op (M.op (M.op X2 X0) (M.op (M.op x y) X2)) x) := by
    intro X0 X2
    first
    | (have i₁ := eq20899 X0 x X2
       have i₂ := eq14 y X0 x
       grind)
    | exact superpose eq14 eq20899
    | exact resolve eq20899 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20899
  have eq21431 : ∀ X0 X2 : G, (M.op y X0) = (M.op (M.op X2 (M.op (M.op x y) (M.op X2 X0))) x) := by
    intro X0 X2
    first
    | (have i₁ := eq21203 X0 X2
       have i₂ := eq5170 (M.op X2 X0) sF0 X2
       grind)
    | (have i₁ := eq21203 X0 X0
       have i₂ := eq5170 X0 sF0 (M.op X0 X0)
       grind)
    | exact superpose eq5170 eq21203
    | exact resolve eq21203 eq5170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21203
  have eq39645 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op x (M.op X0 (M.op x y))) (M.op (M.op (M.op y (M.op (M.op x y) X0)) x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq232 (M.op y (M.op sF0 X1)) X1
       have i₂ := eq1694 sF0 X1
       grind)
    | exact superpose eq1694 eq232
    | exact resolve eq232 eq1694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq39678 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op x (M.op X0 (M.op x y))) (M.op (M.op (M.op X0 x) x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq39645
    | exact resolve eq39645 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39645
  have eq39841 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op x (M.op X0 (M.op x y))) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq39678 X0 X1
       have i₂ := eq6881 X0 x X1
       grind)
    | exact superpose eq6881 eq39678
    | exact resolve eq39678 eq6881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6881 eq39678
  have eq45707 : (M.op (M.op y y) x) = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq5698 y x
       have i₂ := eq5171 sF0
       grind)
    | exact superpose eq5171 eq5698
    | exact resolve eq5698 eq5171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5698
  have eq46362 : (M.op y y) = (M.op (M.op x (M.op (M.op x y) (M.op x y))) x) := by
    first
    | (have i₁ := eq5527 y
       have i₂ := eq45707
       grind)
    | exact superpose eq45707 eq5527
    | exact resolve eq5527 eq45707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5527
  have eq46425 : (M.op x (M.op x (M.op x y))) = (M.op (M.op y y) (M.op y (M.op x (M.op (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq1694 (M.op y y) x
       have i₂ := eq45707
       grind)
    | exact superpose eq45707 eq1694
    | exact resolve eq1694 eq45707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1694 eq45707
  have eq46464 : (M.op x (M.op x (M.op x y))) = (M.op (M.op y y) (M.op (M.op (M.op x y) (M.op x y)) (M.op x y))) := by
    first
    | (have i₁ := eq46425
       have i₂ := eq5171 (M.op sF0 sF0)
       grind)
    | exact superpose eq5171 eq46425
    | exact resolve eq46425 eq5171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5171 eq46425
  have eq46516 : (M.op (M.op y y) (M.op x y)) = (M.op x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq46464
       have i₂ := eq5293 (M.op y y) sF0 sF0
       grind)
    | exact superpose eq5293 eq46464
    | exact resolve eq46464 eq5293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46464
  have eq48343 : (M.op y y) = (M.op (M.op x (M.op x (M.op x y))) (M.op x y)) := by
    first
    | exact superpose eq46516 eq6803
    | exact resolve eq6803 eq46516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6803 eq46516
  have eq299155 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq935 y
       have i₂ := eq8004 x
       grind)
    | exact superpose eq8004 eq935
    | (have j0 := eq935 y
       have j1 := eq8004 x
       grind)
    | exact resolve eq935 eq8004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935 eq8004
  have eq299189 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq299155
       have i₂ := eq114
       grind)
    | exact superpose eq114 eq299155
    | exact resolve eq299155 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299155
  have eq299206 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq299189
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq299189
    | exact resolve eq299189 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299189
  have eq299221 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq21 eq299206
    | exact resolve eq299206 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299206
  have eq299226 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ x) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq299221
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq299221
    | exact resolve eq299221 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299221
  have eq299229 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ x) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq27 eq299226
    | exact resolve eq299226 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299226
  have eq299232 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ x) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq299229
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq299229
    | exact resolve eq299229 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299229
  have eq299235 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ x) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq21 eq299232
    | exact resolve eq299232 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299232
  have eq299238 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ x) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq299235
       have r₂ := eq28
       grind)
    | exact resolve eq299235 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299235
  have eq299241 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq299238
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq299238
    | exact resolve eq299238 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299238
  have eq299249 : (τ (σ (M.op x y))) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq299241 eq131
    | exact resolve eq131 eq299241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq299241
  have eq299533 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq31 eq299249
    | exact resolve eq299249 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq299249
  have eq299729 : (M.op x y) = (M.op y (M.op y (M.op (M.op x y) (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq7334 y y
       have i₂ := eq299533
       grind)
    | exact superpose eq299533 eq7334
    | exact resolve eq7334 eq299533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299533
  have eq299820 : (M.op x y) = (M.op (M.op (M.op x y) y) x) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq5404 eq299729
    | exact resolve eq299729 eq5404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5404 eq299729
  have eq299892 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq5591 eq299820
    | exact resolve eq299820 eq5591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5591 eq299820
  have eq299893 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq299892
  have eq299931 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq64
       have i₂ := eq299893
       grind)
    | exact superpose eq299893 eq64
    | (have r₁ := eq64
       have r₂ := eq299893
       grind)
    | exact resolve eq64 eq299893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq300102 : (M.op y x) = (M.op (M.op x (M.op (M.op x y) (M.op x y))) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq21431 x x
       have i₂ := eq299893
       grind)
    | exact superpose eq299893 eq21431
    | exact resolve eq21431 eq299893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300109 : (M.op x y) = (M.op (M.op x (M.op x (M.op x y))) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq39841 x x
       have i₂ := eq299893
       grind)
    | exact superpose eq299893 eq39841
    | exact resolve eq39841 eq299893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39841 eq299893
  have eq300165 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq299931
  have eq300182 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq48343 eq300109
    | exact resolve eq300109 eq48343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48343 eq300109
  have eq300186 : (M.op y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq46362 eq300102
    | exact resolve eq300102 eq46362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300102
  have eq300247 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq300182
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq300182
    | exact resolve eq300182 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300182
  have eq300381 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq109
       have i₂ := eq300165
       grind)
    | exact superpose eq300165 eq109
    | exact resolve eq109 eq300165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq300165
  have eq300415 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq300381
    | exact resolve eq300381 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300381
  have eq301135 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq300415 eq1237
    | (have j0 := eq1237 (σ (M.op x y)) (M.op (σ y) (σ x))
       grind)
    | exact resolve eq1237 eq300415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237 eq300415
  have eq301140 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq301135
  have eq301149 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq301140
    | exact resolve eq301140 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301140
  have eq301161 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq301149
       have r₂ := eq28
       grind)
    | exact resolve eq301149 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301149
  have eq302919 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq300247
       have i₂ := eq300186
       grind)
    | exact superpose eq300186 eq300247
    | exact resolve eq300247 eq300186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300186 eq300247
  have eq303129 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq302919
  have eq303407 : (M.op x y) = (M.op x (M.op y (M.op (M.op x y) (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq7334 x y
       have i₂ := eq303129
       grind)
    | exact superpose eq303129 eq7334
    | exact resolve eq7334 eq303129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7334 eq303129
  have eq303513 : (M.op x y) = (M.op x (M.op (M.op x y) x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq51 eq303407
    | exact resolve eq303407 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq303407
  have eq338671 : (M.op y (M.op (M.op x y) x)) = (M.op (M.op x (M.op (M.op x y) (M.op x y))) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq303513 eq21431
    | exact resolve eq21431 eq303513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21431 eq303513
  have eq338774 : (M.op y y) = (M.op y (M.op (M.op x y) x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq46362 eq338671
    | exact resolve eq338671 eq46362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46362 eq338671
  have eq338872 : (M.op y y) = (M.op x (M.op (M.op x y) y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq338774
       have i₂ := eq5170 y sF0 x
       grind)
    | (have i₁ := eq338774
       have i₂ := eq5170 x sF0 y
       grind)
    | exact superpose eq5170 eq338774
    | exact resolve eq338774 eq5170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5170 eq338774
  have eq338914 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq5305 eq338872
    | exact resolve eq338872 eq5305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5305 eq338872
  have eq348279 : (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq114
       have i₂ := eq338914
       grind)
    | exact superpose eq338914 eq114
    | exact resolve eq114 eq338914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq338914
  have eq348647 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq348279
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq348279
    | exact resolve eq348279 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq348279
  have eq348922 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq348647 eq7207
    | exact resolve eq7207 eq348647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7207 eq348647
  have eq349054 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq348922
       have i₂ := eq11071 sF2 sF4 sF3 sF2
       grind)
    | (have i₁ := eq348922
       have i₂ := eq11071 sF4 sF2 sF3 sF2
       grind)
    | exact superpose eq11071 eq348922
    | exact resolve eq348922 eq11071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11071 eq348922
  have eq349155 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq5172 eq349054
    | exact resolve eq349054 eq5172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5172 eq349054
  have eq349196 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq349155
       have i₂ := eq5293 sF3 sF2 sF4
       grind)
    | exact superpose eq5293 eq349155
    | exact resolve eq349155 eq5293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5293 eq349155
  have eq349233 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq349196 eq301161
    | exact resolve eq301161 eq349196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301161 eq349196
  have eq349447 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq349233
  have eq349519 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq349447
       have r₂ := eq28
       grind)
    | exact resolve eq349447 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349447
  have eq349560 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq349519 eq30
    | exact resolve eq30 eq349519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq349519
  have eq349764 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq349560
    | exact resolve eq349560 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq349560
  have eq349765 : x = y := by grind
  clear eq349764
  have eq349789 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq349765
       grind)
    | exact superpose eq349765 eq19
    | exact resolve eq19 eq349765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq349790 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq349765
       grind)
    | exact superpose eq349765 eq25
    | exact resolve eq25 eq349765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq349765
  have eq349995 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq349790
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq349790
    | exact resolve eq349790 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq349790
  have eq350030 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq349995 eq27
    | exact resolve eq27 eq349995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq349995
  have eq350741 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq350030 eq72
    | exact resolve eq72 eq350030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq350030
  have eq351088 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq350741
       have i₂ := eq349789
       grind)
    | exact superpose eq349789 eq350741
    | exact resolve eq350741 eq349789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349789 eq350741
  have eq351169 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq351088 eq15
    | exact resolve eq15 eq351088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351088
  have eq351258 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq351169
    | exact resolve eq351169 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq351169
  have eq351280 : False := by grind
  exact eq351280

/-- `Equation3607`: `x ◇ y = z ◇ ((y ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_pxy_x_pxy_Equation3607 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3607 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3607.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq28 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
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
  clear eq19
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X1 X3) X0) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X3 (M.op (M.op X1 X3) X0)
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X2 X3)) X0) X2) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X1 (M.op X2 X3)) X0) X2 X3
       have i₂ := eq9 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) X0) (M.op X3 X1)) = (M.op X2 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X2 X3) X0) (M.op X3 X1) X2
       have i₂ := eq62 X2 X3 X0 X1
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 (M.op (M.op X2 X1) X3))) = (M.op (M.op (M.op X0 X1) X4) (M.op X3 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq63 X4 (M.op (M.op X2 X1) X3) (M.op X3 X2) X0
       have i₂ := eq62 X3 X2 X0 X1
       grind)
    | exact superpose eq62 eq63
    | exact resolve eq63 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X2 (M.op X4 X0)) X1)) = (M.op X4 (M.op (M.op X0 (M.op X1 X2)) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X3 (M.op (M.op X2 (M.op X4 X0)) X1) X4
       have i₂ := eq63 X1 X2 X4 X0
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X3 X4)) = (M.op X2 (M.op (M.op (M.op X1 (M.op X2 X3)) X0) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq77 (M.op (M.op X1 (M.op X2 X3)) X0) X4 X2 X3
       have i₂ := eq9 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq9 eq77
    | exact resolve eq77 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X2 (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X1 X2 X0 (M.op X1 X2)
       have i₂ := eq77 X1 X0 X2 (M.op X1 X2)
       grind)
    | exact superpose eq77 eq62
    | exact resolve eq62 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X2) X4) = (M.op (M.op (M.op X1 X4) (M.op X0 X3)) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 (M.op X0 X3) X1 (M.op X3 X2) X4
       have i₂ := eq77 X1 X2 X0 X3
       grind)
    | exact superpose eq77 eq62
    | exact resolve eq62 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X4 (M.op (M.op X0 X3) X1))) = (M.op (M.op (M.op X0 (M.op X1 X2)) X4) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq63 X4 (M.op (M.op X0 X3) X1) X3 X2
       have i₂ := eq77 X1 X2 X0 X3
       grind)
    | exact superpose eq77 eq63
    | exact resolve eq63 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq77
  have eq218 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X2) X4) = (M.op X1 (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X4) X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq204 X0 X1 X2 X3 X4
       have i₂ := eq88 X1 X4 (M.op X1 X2) X0 (M.op X0 X3)
       grind)
    | exact superpose eq88 eq204
    | exact resolve eq204 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq222 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X3 X4)) = (M.op X2 (M.op X3 (M.op X0 (M.op (M.op X1 X4) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq195 X0 X1 X2 X3 X4
       have i₂ := eq208 X1 X2 X3 X4 X0
       grind)
    | exact superpose eq208 eq195
    | exact resolve eq195 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq208
  have eq229 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X2) X4) = (M.op X1 (M.op X0 (M.op (M.op (M.op X1 X2) X4) (M.op X0 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq218 X0 X1 X2 X3 X4
       have i₂ := eq203 (M.op X0 X3) (M.op (M.op X1 X2) X4) X0
       grind)
    | (have i₁ := eq218 X0 X1 X2 X3 X4
       have i₂ := eq203 X0 (M.op (M.op X1 X2) X4) (M.op X0 X3)
       grind)
    | exact superpose eq203 eq218
    | exact resolve eq218 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq235 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X2) X4) = (M.op X1 (M.op X0 (M.op X1 (M.op X4 (M.op (M.op X3 X2) X0))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq229 X0 X1 X2 X3 X4
       have i₂ := eq88 X1 X2 X3 X0 X4
       grind)
    | exact superpose eq88 eq229
    | exact resolve eq229 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq229
  have eq238 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X2) X4) = (M.op X1 (M.op (M.op X4 X3) (M.op X1 X2))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq235 x X1 X2 X3 X4
       have i₂ := eq222 X4 X3 x X1 X2
       grind)
    | exact superpose eq222 eq235
    | exact resolve eq235 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq235
  have eq279 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq203 X2 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq203 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq203 eq9
    | exact resolve eq9 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X1 X2)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X2 (M.op X1 X0)
       have i₂ := eq203 X2 X1 X0
       grind)
    | (have i₁ := eq9 X3 X2 (M.op X1 X0)
       have i₂ := eq203 X0 X1 X2
       grind)
    | exact superpose eq203 eq9
    | exact resolve eq9 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq308 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (M.op X1 (M.op (M.op X2 (M.op X3 X0)) (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq281 X0 X1 X2 X3
       have i₂ := eq101 X2 X3 X0 (M.op X1 X0) X1
       grind)
    | (have i₁ := eq281 X0 X1 X2 X3
       have i₂ := eq101 X0 X1 X2 X3 (M.op X1 X0)
       grind)
    | exact superpose eq101 eq281
    | exact resolve eq281 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq281
  have eq341 : ∀ X0 X2 X3 : G, (M.op X3 X2) = (M.op (M.op (M.op X3 X0) X0) X2) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq308 X0 x X2 X3
       have i₂ := eq238 x X0 (M.op X3 X0) X2
       grind)
    | (have i₁ := eq308 X0 (M.op X3 X2) X2 X3
       have i₂ := eq238 x X2 X3 (M.op (M.op X2 (M.op X3 X0)) (M.op (M.op X3 X2) X0))
       grind)
    | exact superpose eq238 eq308
    | exact resolve eq308 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238 eq308
  have eq411 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X2 X0 X0 X1
       have i₂ := eq279 (M.op (M.op X0 X1) X2) X2 X0
       grind)
    | exact superpose eq279 eq62
    | exact resolve eq62 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq279
  have eq570 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq411 (M.op X0 X1) X1 X2
       have i₂ := eq341 X1 X2 X0
       grind)
    | exact superpose eq341 eq411
    | exact resolve eq411 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3618 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op X1 X2)) ∨ (M.op (M.op X1 X2) X0) = (k (M.op X1 X2) X0) ∨ (M.op X1 X2) = (M.op X0 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq411 X1 X2 (M.op X1 X2)
       have i₂ := eq14 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq411 X0 X1 X2
       have i₂ := eq14 X0 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq14 eq411
    | (have j1 := eq14 (M.op X1 X2) X0
       grind)
    | exact resolve eq411 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq3625 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op X1 X2)) ∨ (M.op (M.op X1 X2) X0) = (k (M.op X1 X2) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3618 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3618
  have eq3633 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (k (M.op X1 X2) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3625 X0 X1 X2
       have j1 := eq12 (M.op X1 X2) X0
       grind)
    | (have r₁ := eq3625 X1 X1 X2
       have r₂ := eq12 (M.op X1 X2) X1
       grind)
    | exact resolve eq3625 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3625
  have eq3695 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X0 X2) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3633 X0 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq3633 X0 X1 X2
       have i₂ := eq14 X0 (M.op X1 X2)
       grind)
    | exact superpose eq14 eq3633
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq3633 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3730 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X0 X2) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3695 X0 X1 X2
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq3695 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq3695 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3695
  have eq4639 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3730 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3730
  have eq4640 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4639 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4639
  have eq4664 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4640 (σ X0)
       grind)
    | exact superpose eq4640 eq15
    | exact resolve eq15 eq4640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4667 : ∀ X0 X1 : G, (k (M.op (σ X0) (σ X0)) (σ X1)) = (σ (k (k X0 (τ (σ X0))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X0) X1
       have i₂ := eq4640 (σ X0)
       grind)
    | exact superpose eq4640 eq28
    | exact resolve eq28 eq4640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq4684 : ∀ X0 X1 : G, (k (M.op (σ X0) (σ X0)) (σ X1)) = (σ (k (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4667 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4667
    | exact resolve eq4667 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4667
  have eq4687 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4664 X0
       have i₂ := eq4640 X0
       grind)
    | exact superpose eq4640 eq4664
    | exact resolve eq4664 eq4640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4664
  have eq4703 : ∀ X0 X1 : G, (k (M.op (σ X0) (σ X0)) (σ X1)) = (σ (k (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4684 X0 X1
       have i₂ := eq4640 X0
       grind)
    | exact superpose eq4640 eq4684
    | exact resolve eq4684 eq4640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4640 eq4684
  have eq4717 : ∀ X0 X1 : G, (k (M.op (σ X0) (σ X0)) (σ X1)) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4703 X0 X1
       have i₂ := eq3633 X1 X0 X0
       grind)
    | exact superpose eq3633 eq4703
    | exact resolve eq4703 eq3633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4703
  have eq4726 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) (σ X1)) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4717 X0 X1
       have i₂ := eq3633 (σ X1) (σ X0) (σ X0)
       grind)
    | exact superpose eq3633 eq4717
    | exact resolve eq4717 eq3633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4717
  have eq4730 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X1)) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4726 X0 X1
       have i₂ := eq4687 X0
       grind)
    | exact superpose eq4687 eq4726
    | exact resolve eq4726 eq4687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4726
  have eq4831 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (M.op (σ X0) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq570 (σ X0) X1 (σ X0)
       have i₂ := eq4687 X0
       grind)
    | exact superpose eq4687 eq570
    | exact resolve eq570 eq4687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570 eq4687
  have eq4853 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) X1) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4831 X0 X1
       have i₂ := eq4730 X0 X0
       grind)
    | exact superpose eq4730 eq4831
    | exact resolve eq4831 eq4730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4730 eq4831
  have eq5520 : ∀ X0 X1 X2 : G, (σ (k (M.op (M.op X0 X0) X0) X2)) = (k (M.op (M.op (σ X0) X1) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (M.op (M.op X0 X0) X0) X2
       have i₂ := eq4853 X0 X1
       grind)
    | exact superpose eq4853 eq15
    | exact resolve eq15 eq4853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4853
  have eq5547 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ X0) X1) X1) (σ X2)) = (σ (k (M.op (M.op X0 X0) X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5520 X0 X1 X2
       have i₂ := eq3633 (σ X2) (M.op (σ X0) X1) X1
       grind)
    | exact superpose eq3633 eq5520
    | exact resolve eq5520 eq3633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5520
  have eq5660 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ X0) X1) X1) (σ X2)) = (σ (M.op (M.op (M.op X0 X0) X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5547 X0 X1 X2
       have i₂ := eq3633 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq3633 eq5547
    | exact resolve eq5547 eq3633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3633 eq5547
  have eq5730 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ X0) X1) X1) (σ X2)) = (σ (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5660 X0 X1 X2
       have i₂ := eq341 X0 X2 X0
       grind)
    | (have i₁ := eq5660 X0 X1 X2
       have i₂ := eq341 X0 X2 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq341 eq5660
    | exact resolve eq5660 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5660
  have eq5767 : ∀ X0 X2 : G, (σ (M.op X0 X2)) = (M.op (σ X0) (σ X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq5730 X0 x X2
       have i₂ := eq341 x (σ X2) (σ X0)
       grind)
    | (have i₁ := eq5730 X0 x X2
       have i₂ := eq341 X0 (σ X2) (M.op (M.op (σ X0) x) x)
       grind)
    | exact superpose eq341 eq5730
    | exact resolve eq5730 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341 eq5730
  have eq5959 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5767 x y
       grind)
    | exact superpose eq5767 eq16
    | (have r₁ := eq16
       have r₂ := eq5767 x y
       grind)
    | exact resolve eq16 eq5767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5767
  have eq6008 : False := by grind
  exact eq6008

/-- `Equation3607`: `x ◇ y = z ◇ ((y ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pxy_pyx_pxy_Equation3607 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3607 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3607.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq87 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq354 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq87 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq87 X0 X1
       grind)
    | exact superpose eq87 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq87 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq87 X0 X1
       grind)
    | exact resolve eq12 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq87 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq87 X0 X1
       grind)
    | exact superpose eq87 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq87 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq87 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq87 X0 X1
       grind)
    | exact resolve eq13 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq363 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq356 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq371 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq363 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq363 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq363 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq363 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq373 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq354 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq354 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq354 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq385 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq371 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq371
    | (have j0 := eq371 X0 X1
       grind)
    | exact resolve eq371 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq386 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq385 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq387 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq373 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq373
    | (have j0 := eq373 X0 X1
       grind)
    | exact resolve eq373 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq388 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq387 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq394 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq388 X0 X1
       have j1 := eq386 X0 X1
       grind)
    | (have r₁ := eq388 X0 X1
       have r₂ := eq386 X0 X1
       grind)
    | exact resolve eq388 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386 eq388
  have eq395 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq394 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq394
    | exact resolve eq394 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq406 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq394 x y
       grind)
    | exact superpose eq394 eq16
    | exact resolve eq16 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq501 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq395 X0 (τ X1)
       grind)
    | exact superpose eq395 eq18
    | exact resolve eq18 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq395
  have eq532 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq501 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq501
    | exact resolve eq501 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501
  have eq547 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq532 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq532
    | exact resolve eq532 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq586 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq406
       have i₂ := eq547 x y
       grind)
    | exact superpose eq547 eq406
    | exact resolve eq406 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406 eq547
  have eq587 : False := by grind
  exact eq587

/-- `Equation3607`: `x ◇ y = z ◇ ((y ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_pyx_pxy_Equation3607 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3607 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3607.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X2) X0)) := by
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
  have eq53 : ∀ X0 : G, (M.op X0 x) = (M.op y (M.op (M.op x y) X0)) := by
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
  have eq54 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X1 X3) X0) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3 (M.op (M.op X1 X3) X0)
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X2 X3)) X0) X2) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X1 (M.op X2 X3)) X0) X2 X3
       have i₂ := eq14 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq72
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq72
    | exact resolve eq72 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq76 : (M.op x x) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq75
    | exact resolve eq75 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq210 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op (M.op x y) X0) (M.op (M.op X0 x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op X0 (σ x)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq533 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op y X1) x) (M.op (M.op x y) X0)) := by
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
  have eq537 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) X0) X4) = (M.op (M.op (M.op X2 X4) (M.op X3 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 (M.op X3 X1) X2 (M.op (M.op X2 X3) X0) X4
       have i₂ := eq55 X2 X3 X0 X1
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) X0) (M.op X3 X1)) = (M.op X2 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X2 X3) X0) (M.op X3 X1) X2
       have i₂ := eq55 X2 X3 X0 X1
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq651 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 (M.op (M.op X2 X1) X3))) = (M.op (M.op (M.op X0 X1) X4) (M.op X3 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 X4 (M.op (M.op X2 X1) X3) (M.op X3 X2) X0
       have i₂ := eq55 X3 X2 X0 X1
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq656 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X4 (M.op X3 (M.op X4 X0)))) = (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 X4 (M.op X3 (M.op X4 X0)) X1 X2
       have i₂ := eq56 (M.op X1 X2) X3 X4 X0
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq659 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op (M.op (M.op X1 X4) (M.op X2 (M.op X3 X0))) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 (M.op X2 (M.op X3 X0)) X1 X3 X4
       have i₂ := eq56 X1 X2 X3 X0
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq660 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X1) = (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X4 (M.op X2 (M.op X4 X0))) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X4 (M.op X2 (M.op X4 X0)) X3 X1
       have i₂ := eq56 X1 X2 X4 X0
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 (M.op X3 X0))) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op X2 (M.op X3 X0)) X1
       have i₂ := eq56 X1 X2 X3 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq3831 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X2 (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq539 X1 X0 X2 (M.op X1 X2)
       have i₂ := eq55 X1 X2 X0 (M.op X1 X2)
       grind)
    | exact superpose eq55 eq539
    | exact resolve eq539 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq3832 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op y (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq533 eq539
    | exact resolve eq539 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3901 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3831 X2 (M.op X1 X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq3831
    | exact resolve eq3831 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3912 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq54 eq3831
    | exact resolve eq3831 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq4270 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 x)) = (M.op X1 (M.op X0 (M.op X1 y))) := by
    intro X0 X1
    first
    | exact superpose eq53 eq661
    | exact resolve eq661 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq4382 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op x y))) = (M.op X1 (M.op X0 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq4270 X1 X1
       have i₂ := eq3831 sF0 X1 x
       grind)
    | (have i₁ := eq4270 X1 X1
       have i₂ := eq3831 x X1 sF0
       grind)
    | exact superpose eq3831 eq4270
    | exact resolve eq4270 eq3831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4270
  have eq4445 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = (M.op X1 (M.op (M.op X0 X1) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq3912 eq14
    | exact resolve eq14 eq3912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3912
  have eq4468 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq4445 x x
       have i₂ := eq14 sF2 x x
       grind)
    | exact superpose eq14 eq4445
    | exact resolve eq4445 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4445
  have eq7695 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) X0) X4) = (M.op X1 (M.op X0 (M.op (M.op X2 X4) (M.op X3 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq537 X0 X1 X2 X3 X4
       have i₂ := eq3831 (M.op (M.op X2 X4) (M.op X3 X1)) X0 X1
       grind)
    | (have i₁ := eq537 X0 X1 X2 X3 X4
       have i₂ := eq3831 X1 X0 (M.op (M.op X2 X4) (M.op X3 X1))
       grind)
    | exact superpose eq3831 eq537
    | exact resolve eq537 eq3831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq8991 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op y (M.op x (M.op (M.op X0 X1) (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq533 x X1
       have i₂ := eq651 y X1 x sF0 x
       grind)
    | exact superpose eq651 eq533
    | exact resolve eq533 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq9107 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op x y)) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq8991 X0 X1
       have i₂ := eq3832 (M.op (M.op X0 X1) sF0)
       grind)
    | exact superpose eq3832 eq8991
    | exact resolve eq8991 eq3832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8991
  have eq11060 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op (M.op X1 X2) (M.op X0 (M.op (M.op X1 X4) (M.op X2 (M.op X3 X0))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq659 X0 X1 X2 X3 X4
       have i₂ := eq3831 (M.op (M.op X1 X4) (M.op X2 (M.op X3 X0))) X0 (M.op X1 X2)
       grind)
    | (have i₁ := eq659 X0 X1 X2 X3 X4
       have i₂ := eq3831 (M.op X1 X2) X0 (M.op (M.op X1 X4) (M.op X2 (M.op X3 X0)))
       grind)
    | exact superpose eq3831 eq659
    | exact resolve eq659 eq3831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq11447 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 X4) = (M.op (M.op (M.op X5 X0) (M.op X4 X5)) (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X2)) X1) X3)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq660 (M.op X5 X0) X4 X5 X3 X2
       have i₂ := eq656 X0 X1 X2 X2 X5
       grind)
    | exact superpose eq656 eq660
    | exact resolve eq660 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656 eq660
  have eq11649 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 X4) = (M.op X5 (M.op (M.op X4 X5) (M.op (M.op X3 X0) (M.op (M.op X0 (M.op (M.op X1 X2) X2)) X1)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq11447 X0 X1 X2 X3 X4 X5
       have i₂ := eq651 X5 X0 X3 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) X1) (M.op X4 X5)
       grind)
    | exact superpose eq651 eq11447
    | exact resolve eq11447 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651 eq11447
  have eq11780 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op (M.op (M.op X3 X0) (M.op (M.op X0 (M.op (M.op X1 X2) X2)) X1)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq11649 X0 X1 X2 X3 X4 x
       have i₂ := eq14 (M.op (M.op X3 X0) (M.op (M.op X0 (M.op (M.op X1 X2) X2)) X1)) X4 x
       grind)
    | exact superpose eq14 eq11649
    | exact resolve eq11649 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11649
  have eq11816 : ∀ X0 X1 X3 X4 : G, (M.op X3 X4) = (M.op (M.op (M.op X3 X0) (M.op (M.op X0 X1) X1)) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq11780 X0 X1 x X3 X4
       have i₂ := eq3901 X0 X1 x
       grind)
    | exact superpose eq3901 eq11780
    | exact resolve eq11780 eq3901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11780
  have eq11830 : ∀ X0 X3 X4 : G, (M.op X3 X4) = (M.op (M.op (M.op X3 X0) X0) X4) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq11816 X0 x X3 X4
       have i₂ := eq3901 (M.op X3 X0) X0 x
       grind)
    | exact superpose eq3901 eq11816
    | exact resolve eq11816 eq3901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3901 eq11816
  have eq11965 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op (M.op x y) (M.op X0 x)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq210 (M.op X0 x) X1
       have i₂ := eq11830 x X0 X1
       grind)
    | exact superpose eq11830 eq210
    | exact resolve eq210 eq11830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12177 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op x (M.op X0 (M.op x y))) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11965 X1 X1
       have i₂ := eq3831 sF0 X1 x
       grind)
    | (have i₁ := eq11965 X1 X1
       have i₂ := eq3831 x X1 sF0
       grind)
    | exact superpose eq3831 eq11965
    | exact resolve eq11965 eq3831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11965
  have eq14975 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X4 (M.op X0 (M.op X1 X2)))) = (M.op (M.op (M.op (M.op X0 X3) X3) X4) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7695 X4 X2 (M.op X0 X3) X3 X1
       have i₂ := eq539 X1 X2 X0 X3
       grind)
    | exact superpose eq539 eq7695
    | exact resolve eq7695 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq15017 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X1) X2)) = (M.op (M.op (M.op X2 X0) X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7695 X3 X1 X2 X0 X3
       have i₂ := eq14 (M.op X0 X1) X2 X3
       grind)
    | exact superpose eq14 eq7695
    | exact resolve eq7695 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7695
  have eq15345 : ∀ X0 X2 X3 : G, (M.op X2 X0) = (M.op (M.op (M.op X2 X0) X3) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq15017 X0 x X2 X3
       have i₂ := eq14 X2 X0 x
       grind)
    | exact superpose eq14 eq15017
    | exact resolve eq15017 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15017
  have eq15369 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X4) X1) = (M.op X2 (M.op X4 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq14975 X0 X1 X2 x X4
       have i₂ := eq11830 x X0 X4
       grind)
    | (have i₁ := eq14975 X0 X1 X2 x X4
       have i₂ := eq11830 X0 (M.op (M.op X0 x) x) X4
       grind)
    | exact superpose eq11830 eq14975
    | exact resolve eq14975 eq11830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11830 eq14975
  have eq16008 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X4 (M.op X2 (M.op X4 X3))) (M.op X1 (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq11060 X1 X4 (M.op X2 (M.op X4 X3)) X0 X3
       have i₂ := eq14 (M.op X0 X1) X2 (M.op X4 X3)
       grind)
    | exact superpose eq14 eq11060
    | exact resolve eq11060 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11060
  have eq16280 : ∀ X0 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X4 (M.op X2 (M.op X4 X3))) (M.op X2 X0)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq16008 X0 x X2 X3 X4
       have i₂ := eq14 X2 X0 x
       grind)
    | exact superpose eq14 eq16008
    | exact resolve eq16008 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16008
  have eq16951 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op X0 X1)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq210 (M.op X0 X1) x
       have i₂ := eq15345 X1 X0 x
       grind)
    | exact superpose eq15345 eq210
    | (have j1 := eq15345 y x (M.op X0 X1)
       grind)
    | exact resolve eq210 eq15345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq16957 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq212 (M.op x X0) sF2
       have i₂ := eq15345 X0 x sF2
       grind)
    | exact superpose eq15345 eq212
    | (have j1 := eq15345 (σ y) (σ x) (M.op X0 X1)
       grind)
    | exact resolve eq212 eq15345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq15345
  have eq17139 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X1 (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq16957 X1 x
       have i₂ := eq3831 (M.op sF4 (M.op X1 x)) X1 x
       grind)
    | (have i₁ := eq16957 X1 X0
       have i₂ := eq3831 X0 X1 (M.op sF4 (M.op X1 X0))
       grind)
    | exact superpose eq3831 eq16957
    | exact resolve eq16957 eq3831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16957
  have eq17144 : ∀ X0 X1 : G, (M.op x y) = (M.op X1 (M.op X0 (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq16951 X1 x
       have i₂ := eq3831 (M.op sF0 (M.op X1 x)) X1 x
       grind)
    | (have i₁ := eq16951 X1 X0
       have i₂ := eq3831 X0 X1 (M.op sF0 (M.op X1 X0))
       grind)
    | exact superpose eq3831 eq16951
    | exact resolve eq16951 eq3831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3831 eq16951
  have eq17221 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X1 (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq17139
    | (have j0 := eq17139 X0 X1
       grind)
    | exact resolve eq17139 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17139
  have eq17224 : ∀ X0 X1 : G, (M.op x y) = (M.op X1 (M.op X0 (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17144 X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17144
    | (have j0 := eq17144 X0 X1
       grind)
    | exact resolve eq17144 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17144
  have eq49859 : (M.op (M.op y y) (M.op x y)) = (M.op x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq4382 x y
       have i₂ := eq3832 (M.op y y)
       grind)
    | exact superpose eq3832 eq4382
    | exact resolve eq4382 eq3832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3832 eq4382
  have eq50794 : (M.op y y) = (M.op (M.op x (M.op x (M.op x y))) (M.op x y)) := by
    first
    | exact superpose eq49859 eq9107
    | exact resolve eq9107 eq49859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9107 eq49859
  have eq71680 : (M.op x y) = (M.op x (M.op y (M.op (M.op x y) (M.op x x)))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq17224 y x
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq17224
    | exact resolve eq17224 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq17224
  have eq71696 : (M.op x y) = (M.op x (M.op (M.op x x) x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq53 eq71680
    | exact resolve eq71680 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq71680
  have eq71747 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq71696
       have i₂ := eq14 x x x
       grind)
    | exact superpose eq14 eq71696
    | exact resolve eq71696 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71696
  have eq139688 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq71747 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq71747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139689 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq139688
    | exact resolve eq139688 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139688
  have eq139701 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq139689
       have r₂ := eq28
       grind)
    | exact resolve eq139689 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139689
  have eq139720 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq139701 eq12
    | (have j0 := eq12 (σ x) (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq139701
       grind)
    | exact resolve eq12 eq139701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139791 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq139701 eq17221
    | exact resolve eq17221 eq139701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139701
  have eq139807 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq139720
  have eq139808 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq139807
  have eq139820 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq139791
       have i₂ := eq15369 sF4 sF2 sF2 sF3
       grind)
    | exact superpose eq15369 eq139791
    | exact resolve eq139791 eq15369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139791
  have eq139893 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq4468 eq139820
    | exact resolve eq139820 eq4468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139820
  have eq140739 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq139808 eq71747
    | exact resolve eq71747 eq139808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71747 eq139808
  have eq140747 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq140739
  have eq140772 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq140747 eq139893
    | exact resolve eq139893 eq140747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139893 eq140747
  have eq140882 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq140772
  have eq140935 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq140882
       have r₂ := eq28
       grind)
    | exact resolve eq140882 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140882
  have eq140970 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq52
       have i₂ := eq140935
       grind)
    | exact superpose eq140935 eq52
    | exact resolve eq52 eq140935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq141056 : (M.op x y) = (M.op (M.op x (M.op x (M.op x y))) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12177 x x
       have i₂ := eq140935
       grind)
    | exact superpose eq140935 eq12177
    | exact resolve eq12177 eq140935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141064 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op x (M.op X1 (M.op x y))) (M.op X1 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq16280 X0 X1 x x
       have i₂ := eq140935
       grind)
    | exact superpose eq140935 eq16280
    | exact resolve eq16280 eq140935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16280
  have eq141102 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq12177 eq141064
    | exact resolve eq141064 eq12177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12177 eq141064
  have eq141106 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq50794 eq141056
    | exact resolve eq141056 eq50794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50794 eq141056
  have eq141150 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq140970
    | exact resolve eq140970 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140970
  have eq141153 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq141106
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq141106
    | exact resolve eq141106 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141106
  have eq144705 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq141153
       have i₂ := eq141102 y
       grind)
    | exact superpose eq141102 eq141153
    | exact resolve eq141153 eq141102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141102 eq141153
  have eq144763 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq144705
  have eq145149 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq144763
       grind)
    | exact superpose eq144763 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq144763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144763
  have eq145234 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq145149
  have eq145275 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq145234
       have r₂ := eq140935
       grind)
    | exact resolve eq145234 eq140935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140935 eq145234
  have eq147767 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq49
       have i₂ := eq145275
       grind)
    | exact superpose eq145275 eq49
    | exact resolve eq49 eq145275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq145275
  have eq147799 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq147767
    | exact resolve eq147767 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147767
  have eq147865 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq147799 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq147799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147799
  have eq147866 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq147865
  have eq147870 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq147866
    | exact resolve eq147866 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147866
  have eq147882 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq147870
       have r₂ := eq28
       grind)
    | exact resolve eq147870 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147870
  have eq179770 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq147882 eq17221
    | exact resolve eq17221 eq147882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17221 eq147882
  have eq179799 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq179770
       have i₂ := eq15369 sF4 sF2 sF2 sF3
       grind)
    | exact superpose eq15369 eq179770
    | exact resolve eq179770 eq15369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15369 eq179770
  have eq179880 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq4468 eq179799
    | exact resolve eq179799 eq4468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4468 eq179799
  have eq181864 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq179880 eq141150
    | exact resolve eq141150 eq179880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141150 eq179880
  have eq181984 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq181864
  have eq182046 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq181984
       have r₂ := eq28
       grind)
    | exact resolve eq181984 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181984
  have eq182082 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq182046 eq30
    | exact resolve eq30 eq182046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq182046
  have eq182276 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq182082
    | exact resolve eq182082 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq182082
  have eq182277 : x = y := by grind
  clear eq182276
  have eq182299 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq182277
       grind)
    | exact superpose eq182277 eq19
    | exact resolve eq19 eq182277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq182300 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq182277
       grind)
    | exact superpose eq182277 eq25
    | exact resolve eq25 eq182277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq182277
  have eq182499 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq182300
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq182300
    | exact resolve eq182300 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq182300
  have eq182538 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq182499 eq27
    | exact resolve eq27 eq182499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq182499
  have eq183088 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq182538 eq68
    | exact resolve eq68 eq182538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq182538
  have eq183297 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq183088
       have i₂ := eq182299
       grind)
    | exact superpose eq182299 eq183088
    | exact resolve eq183088 eq182299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182299 eq183088
  have eq185826 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq183297 eq15
    | exact resolve eq15 eq183297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183297
  have eq185911 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq185826
    | exact resolve eq185826 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq185826
  have eq185932 : False := by grind
  exact eq185932
