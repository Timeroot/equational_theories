import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_pxy_pyy_pxx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  clear eq17
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
  have eq61 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
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
  have eq72 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq61 X1 X0 X3
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq278 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq278 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq278 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq278 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq290 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq279 (σ X0)
       grind)
    | exact superpose eq279 eq15
    | exact resolve eq15 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq309 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq290 X0
       have i₂ := eq279 X0
       grind)
    | exact superpose eq279 eq290
    | exact resolve eq290 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279 eq290
  have eq343 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq309 X0
       grind)
    | exact superpose eq309 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq482 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq505 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq482 X0 X1
       have i₂ := eq309 X0
       grind)
    | exact superpose eq309 eq482
    | (have j0 := eq482 X0 X1
       grind)
    | exact resolve eq482 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq517 : ∀ X0 X1 : G, (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (M.op (σ X0) (σ X0))) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq505 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq505
    | (have j0 := eq505 (σ X0) (σ X1)
       grind)
    | exact resolve eq505 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq561 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq517 X0 X1
       have i₂ := eq309 X0
       grind)
    | exact superpose eq309 eq517
    | (have j0 := eq517 X0 X1
       grind)
    | exact resolve eq517 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq4830 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq72 x X2 X0 X1
       grind)
    | exact superpose eq72 eq9
    | exact resolve eq9 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq4947 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4830 X0 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq4830 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq4830 eq4830
    | exact resolve eq4830 eq4830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4830
  have eq17263 : ∀ X0 X1 : G, (σ (M.op (σ X0) (σ X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (σ (σ (M.op X0 X0))) = (σ (σ X1)) ∨ (σ (M.op (σ X0) (σ X0))) = (k (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq343 (σ X0) (σ (σ X1))
       have i₂ := eq561 X0 X1
       grind)
    | exact superpose eq561 eq343
    | (have j0 := eq343 (σ X0) (σ (σ X1))
       have j1 := eq561 X0 X1
       grind)
    | exact resolve eq343 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq17371 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) ≠ (σ (σ (k X0 X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq561 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17372 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) ≠ (σ (σ X1)) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq561 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq17448 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (σ (σ (M.op X0 X0))) = (σ (σ X1)) ∨ (σ (M.op (σ X0) (σ X0))) = (k (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17263 X0 X1
       have i₂ := eq309 X0
       grind)
    | exact superpose eq309 eq17263
    | (have j0 := eq17263 X0 X1
       grind)
    | exact resolve eq17263 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17263
  have eq17449 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (σ (σ X1)) ∨ (σ (M.op (σ X0) (σ X0))) = (k (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq17448 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17448
  have eq17583 : ∀ X0 X1 : G, (σ (M.op (σ X0) (σ X0))) = (σ (k (σ X0) (σ X1))) ∨ (σ (σ (M.op X0 X0))) = (σ (σ X1)) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17449 X0 X1
       have i₂ := eq15 (σ X0) (σ X1)
       grind)
    | exact superpose eq15 eq17449
    | (have j0 := eq17449 X0 X1
       grind)
    | exact resolve eq17449 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17449
  have eq17646 : ∀ X0 X1 : G, (σ (M.op (σ X0) (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ (M.op X0 X0))) = (σ (σ X1)) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17583 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq17583
    | (have j0 := eq17583 X0 X1
       grind)
    | exact resolve eq17583 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17583
  have eq17694 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ (M.op X0 X0))) = (σ (σ X1)) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17646 X0 X1
       have i₂ := eq309 X0
       grind)
    | exact superpose eq309 eq17646
    | (have j0 := eq17646 X0 X1
       grind)
    | exact resolve eq17646 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17646
  have eq17714 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (σ (σ (k X0 X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq17694 X0 X1
       have j1 := eq17372 X0 X1
       grind)
    | (have r₁ := eq17694 X0 X1
       have r₂ := eq17372 X0 (k X0 X1)
       grind)
    | (have r₁ := eq17694 X0 X1
       have r₂ := eq17372 X0 X1
       grind)
    | (have r₁ := eq17694 X0 (M.op X0 X0)
       have r₂ := eq17372 X0 (M.op X0 X0)
       grind)
    | exact resolve eq17694 eq17372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17372 eq17694
  have eq17731 : ∀ X0 X2 : G, (M.op (σ (σ X0)) (σ (σ X2))) = (σ (σ (k X0 X2))) ∨ (σ (σ X2)) = (M.op (σ (σ X0)) (σ (σ X2))) := by
    intro X0 X2
    first
    | (have j0 := eq17714 X0 X2
       have j1 := eq17371 X0 X2
       grind)
    | (have r₁ := eq17714 X0 x
       have r₂ := eq17371 X0 x
       grind)
    | exact resolve eq17714 eq17371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17371 eq17714
  have eq17768 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ X0)) = (σ (σ (k X1 (τ X0)))) ∨ (σ X0) = (M.op (σ (σ X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17731 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17731
    | exact resolve eq17731 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17731
  have eq18010 : ∀ X0 X1 : G, (σ (k (σ X1) X0)) = (M.op (σ (σ X1)) (σ X0)) ∨ (σ X0) = (M.op (σ (σ X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17768 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq17768
    | (have j0 := eq17768 X0 X1
       grind)
    | exact resolve eq17768 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq17768
  have eq21121 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18010 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18010
    | exact resolve eq18010 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18010
  have eq21351 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq21121 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq21121
    | (have j0 := eq21121 (τ X0) (τ X1)
       grind)
    | exact resolve eq21121 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq21564 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq21351 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq21351
    | (have j0 := eq21351 X0 X1
       grind)
    | exact resolve eq21351 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21351
  have eq21620 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq21564 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21564
    | (have j0 := eq21564 X0 X1
       grind)
    | exact resolve eq21564 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21564
  have eq21654 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq21620 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq21620
    | (have j0 := eq21620 X0 X1
       grind)
    | exact resolve eq21620 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21620
  have eq21687 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq21654 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21654
    | (have j0 := eq21654 X0 X1
       grind)
    | exact resolve eq21654 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21654
  have eq21704 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21687 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21687
    | (have j0 := eq21687 X0 X1
       grind)
    | exact resolve eq21687 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21687
  have eq21764 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21121 X0 X1
       have i₂ := eq21704 X0 X1
       grind)
    | exact superpose eq21704 eq21121
    | (have j0 := eq21121 X0 X1
       have j1 := eq21704 (σ X0) (σ X1)
       grind)
    | exact resolve eq21121 eq21704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67245 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21764 x y
       grind)
    | exact superpose eq21764 eq16
    | (have j1 := eq21764 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq21764 x y
       grind)
    | exact resolve eq16 eq21764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21764
  have eq67370 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq67245
  have eq67532 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67370
       grind)
    | exact superpose eq67370 eq16
    | exact resolve eq16 eq67370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67541 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq67370
       grind)
    | exact superpose eq67370 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq67370
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq67370
       grind)
    | exact resolve eq12 eq67370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67542 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4947 (σ y) (σ x)
       have i₂ := eq67370
       grind)
    | exact superpose eq67370 eq4947
    | exact resolve eq4947 eq67370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67370
  have eq67556 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq67541
  have eq67558 : (σ y) = (σ (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq67542
       have i₂ := eq309 y
       grind)
    | exact superpose eq309 eq67542
    | exact resolve eq67542 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67542
  have eq67559 : (σ (M.op y y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq67556
       have i₂ := eq309 y
       grind)
    | exact superpose eq309 eq67556
    | exact resolve eq67556 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309 eq67556
  have eq67561 : (σ (M.op y y)) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq67559
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq67559
    | exact resolve eq67559 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67559
  have eq67562 : (σ (M.op x y)) = (σ (M.op y y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21704 eq67561
    | (have j1 := eq21704 x y
       grind)
    | exact resolve eq67561 eq21704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21704 eq67561
  have eq67588 : (τ (σ y)) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq67558
       grind)
    | exact superpose eq67558 eq10
    | exact resolve eq10 eq67558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67558
  have eq67813 : y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq67588
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq67588
    | exact resolve eq67588 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67588
  have eq67966 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq67813 eq67562
    | exact resolve eq67562 eq67813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67562 eq67813
  have eq67967 : y = (M.op x y) := by
    first
    | (have r₁ := eq67966
       have r₂ := eq67532
       grind)
    | exact resolve eq67966 eq67532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67532 eq67966
  have eq67968 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67967
       grind)
    | exact superpose eq67967 eq16
    | exact resolve eq16 eq67967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67969 : y ≠ y ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq67967
       grind)
    | exact superpose eq67967 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq67967
       grind)
    | exact resolve eq12 eq67967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67970 : y = (M.op y y) := by
    first
    | (have i₁ := eq4947 y x
       have i₂ := eq67967
       grind)
    | exact superpose eq67967 eq4947
    | exact resolve eq4947 eq67967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4947 eq67967
  have eq67984 : (k x y) = (M.op y y) := by grind
  clear eq67969
  have eq68119 : y = (k x y) := by
    first
    | (have i₁ := eq67984
       have i₂ := eq67970
       grind)
    | exact superpose eq67970 eq67984
    | exact resolve eq67984 eq67970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67970 eq67984
  have eq68131 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21121 x y
       have i₂ := eq68119
       grind)
    | exact superpose eq68119 eq21121
    | (have j0 := eq21121 x y
       grind)
    | exact resolve eq21121 eq68119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21121 eq68119
  have eq68165 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq68131
  have eq68196 : False := by grind
  exact eq68196

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_pyy_pyy_pyx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq61 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
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
  have eq62 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
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
  have eq72 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq61 X1 X0 X3
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq276 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq276 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq276 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq288 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq277 (σ X0)
       grind)
    | exact superpose eq277 eq15
    | exact resolve eq15 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq295 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq277 (τ X0)
       grind)
    | exact superpose eq277 eq17
    | exact resolve eq17 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq300 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq295 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq295
    | exact resolve eq295 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq307 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq288 X0
       have i₂ := eq277 X0
       grind)
    | exact superpose eq277 eq288
    | exact resolve eq288 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq320 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq300 X0
       have i₂ := eq277 X0
       grind)
    | exact superpose eq277 eq300
    | exact resolve eq300 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277 eq300
  have eq342 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq307 X0
       grind)
    | exact superpose eq307 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op X0 X0))) = (M.op (M.op X1 (σ (M.op X0 X0))) (M.op X2 (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 (σ X0) X1 X2
       have i₂ := eq307 X0
       grind)
    | exact superpose eq307 eq61
    | exact resolve eq61 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq62 (σ X0)
       have i₂ := eq307 X0
       grind)
    | exact superpose eq307 eq62
    | exact resolve eq62 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq346 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op X1 (M.op X2 (σ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq307 X0
       grind)
    | exact superpose eq307 eq9
    | exact resolve eq9 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq320 X0
       grind)
    | exact superpose eq320 eq10
    | exact resolve eq10 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq368 : ∀ X0 X1 X2 : G, (M.op X1 (τ (M.op X0 X0))) = (M.op (M.op X1 (τ (M.op X0 X0))) (M.op X2 (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 (τ X0) X1 X2
       have i₂ := eq359 X0
       grind)
    | exact superpose eq359 eq61
    | exact resolve eq61 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq448 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq423 X0 X1
       have i₂ := eq307 X1
       grind)
    | exact superpose eq307 eq423
    | (have j0 := eq423 X0 X1
       grind)
    | exact resolve eq423 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq462 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq448 X0 X1
       have i₂ := eq307 X0
       grind)
    | exact superpose eq307 eq448
    | (have j0 := eq448 X0 X1
       grind)
    | exact resolve eq448 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq475 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op X1 (σ (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq346 X0 X1 (σ (M.op X0 X0))
       have i₂ := eq307 (M.op X0 X0)
       grind)
    | exact superpose eq307 eq346
    | exact resolve eq346 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq510 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq462 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq462
    | (have j0 := eq462 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | exact resolve eq462 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq511 : ∀ X0 X1 : G, (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (M.op (σ X0) (σ X0))) = (σ (M.op (σ X1) (σ X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq462 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq462
    | (have j0 := eq462 (σ X0) (σ X1)
       grind)
    | exact resolve eq462 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq554 : ∀ X0 X1 : G, (σ (M.op (σ X0) (σ X0))) = (σ (σ (M.op X1 X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq511 X0 X1
       have i₂ := eq307 X1
       grind)
    | exact superpose eq307 eq511
    | (have j0 := eq511 X0 X1
       grind)
    | exact resolve eq511 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq572 : ∀ X0 X1 : G, (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ (M.op X0 X0))) = (σ (σ (M.op X1 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq554 X0 X1
       have i₂ := eq307 X0
       grind)
    | exact superpose eq307 eq554
    | (have j0 := eq554 X0 X1
       grind)
    | exact resolve eq554 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq667 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq475 X0 (σ (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq307 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq307 eq475
    | exact resolve eq475 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq804 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (τ (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq368 X0 (τ (M.op X0 X0)) x
       have i₂ := eq359 (M.op X0 X0)
       grind)
    | exact superpose eq359 eq368
    | exact resolve eq368 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq4163 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq342 X1 (σ X0)
       have i₂ := eq307 X0
       grind)
    | exact superpose eq307 eq342
    | (have j0 := eq342 X1 (σ X0)
       grind)
    | (have r₁ := eq342 X0 (σ X0)
       have r₂ := eq307 X0
       grind)
    | exact resolve eq342 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq4172 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4163 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4163
    | (have j0 := eq4163 X0 X1
       grind)
    | exact resolve eq4163 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4163
  have eq5309 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq72 x X2 X0 X1
       grind)
    | exact superpose eq72 eq9
    | exact resolve eq9 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq5429 : ∀ X0 X1 X2 : G, (M.op X1 (τ X0)) = (M.op (M.op X1 (τ X0)) (M.op X2 (M.op (τ (M.op (M.op X0 X0) (M.op X0 X0))) (τ (M.op (M.op X0 X0) (M.op X0 X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5309 X0 (τ (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X1 (τ X0))
       have i₂ := eq804 X0 X1
       grind)
    | exact superpose eq804 eq5309
    | exact resolve eq5309 eq804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq5431 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5309 X0 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq5309 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq5309 eq5309
    | exact resolve eq5309 eq5309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5448 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X2 X0
       have i₂ := eq5309 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq5309 eq9
    | exact resolve eq9 eq5309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5457 : ∀ X0 X1 X2 : G, (M.op X1 (τ X0)) = (M.op (M.op X1 (τ X0)) (M.op X2 (τ (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5429 X0 X1 X2
       have i₂ := eq359 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq359 eq5429
    | exact resolve eq5429 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5429
  have eq5985 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5309 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) X1 X2
       have i₂ := eq5448 (M.op X1 X2) X0 (M.op X1 X2)
       grind)
    | exact superpose eq5448 eq5309
    | exact resolve eq5309 eq5448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5309 eq5448
  have eq6130 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2 X3
    by_contra hcon
    push Not at hcon
    have f6130_12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
      intro X0 X1 X2
      grind
    have f6130_13 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))) = X2 := by
      intro X0 X1 X2
      grind
    have f6130_22 : X0 ≠ (M.op X0 (M.op X3 (M.op X1 (M.op X2 X0)))) := by grind
    have f6130_81 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 (M.op X1 (M.op X2 X0)))) = X0 := by
      intro X0 X1 X2 X3
      first
      | (have i₁ := f6130_12 (M.op X0 (M.op X1 X2)) X2 X2
         have i₂ := f6130_13 X0 X1 X2
         grind)
      | exact superpose f6130_13 f6130_12
      | exact resolve f6130_12 f6130_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f6130_213 : X0 ≠ X0 := by
      first
      | (have i₁ := f6130_22
         have i₂ := f6130_81 X0 X1 X2 X3
         grind)
      | exact superpose f6130_81 f6130_22
      | (have r₁ := f6130_22
         have r₂ := f6130_81 X0 X1 X2 X3
         grind)
      | exact resolve f6130_22 f6130_81
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f6130_214 : False := by grind
    exact f6130_214
  clear eq61
  have eq6131 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 X0)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 (M.op X2 X0)) X3 X0
       have i₂ := eq5985 X1 X2 X0
       grind)
    | exact superpose eq5985 eq9
    | exact resolve eq9 eq5985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5985
  have eq6166 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (σ X1)) = (M.op (M.op X2 (σ X1)) (M.op X3 (M.op X4 (M.op X0 (σ (M.op X1 X1)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6130 (M.op X2 (σ X1)) X4 (M.op X0 (σ (M.op X1 X1))) X3
       have i₂ := eq343 X1 X0 X2
       grind)
    | exact superpose eq343 eq6130
    | exact resolve eq6130 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10480 : ∀ X0 X1 : G, (σ (σ X1)) ≠ (σ (σ (k X0 X1))) ∨ (σ (σ (M.op X0 X0))) = (σ (σ (M.op X1 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq572 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq11160 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq510 x y
       grind)
    | exact superpose eq510 eq16
    | (have j1 := eq510 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq510 x y
       grind)
    | exact resolve eq16 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq11204 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq11160
  have eq25890 : (M.op y y) = (τ (σ (M.op x x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq11204
       grind)
    | exact superpose eq11204 eq10
    | exact resolve eq10 eq11204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11204
  have eq26069 : (M.op x x) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25890
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq25890
    | exact resolve eq25890 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25890
  have eq26070 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq26069
  have eq26072 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26070
       grind)
    | exact superpose eq26070 eq16
    | exact resolve eq16 eq26070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26084 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq26070
       grind)
    | exact superpose eq26070 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq26070
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq26070
       grind)
    | exact resolve eq12 eq26070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26085 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5431 (σ y) (σ x)
       have i₂ := eq26070
       grind)
    | exact superpose eq26070 eq5431
    | exact resolve eq5431 eq26070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26070
  have eq26103 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq26084
  have eq26106 : (σ y) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26085
       have i₂ := eq307 y
       grind)
    | exact superpose eq307 eq26085
    | exact resolve eq26085 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26085
  have eq26107 : (M.op (σ y) (σ y)) = (σ (k x y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26103
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq26103
    | exact resolve eq26103 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26103
  have eq26108 : (σ (M.op y y)) = (σ (k x y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26107
       have i₂ := eq307 y
       grind)
    | exact superpose eq307 eq26107
    | exact resolve eq26107 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26107
  have eq26109 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14 eq26108
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq26108 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26108
  have eq26140 : (M.op y y) = (τ (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq26106
       grind)
    | exact superpose eq26106 eq10
    | exact resolve eq10 eq26106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26106
  have eq26319 : (M.op x x) = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26140
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq26140
    | exact resolve eq26140 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26140
  have eq26475 : (σ (M.op x y)) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26319 eq26109
    | exact resolve eq26109 eq26319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26109 eq26319
  have eq26476 : (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq26475
       have r₂ := eq26072
       grind)
    | exact resolve eq26475 eq26072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26072 eq26475
  have eq26479 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op y X0) = X0 ∨ (k y X0) = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq26476
       grind)
    | exact superpose eq26476 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq26476
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq26476
       grind)
    | exact resolve eq13 eq26476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26480 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ y = (M.op X0 y) ∨ (k X0 y) = (M.op y X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq26476
       grind)
    | exact superpose eq26476 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq26476
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq26476
       grind)
    | exact resolve eq13 eq26476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26486 : ∀ X0 X1 : G, (M.op X0 (σ (M.op x x))) = (M.op (M.op X0 (σ (M.op x x))) (M.op X1 (σ y))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq343 y X1 x
       have i₂ := eq26476
       grind)
    | exact superpose eq26476 eq343
    | exact resolve eq343 eq26476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq26487 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq345 y
       have i₂ := eq26476
       grind)
    | exact superpose eq26476 eq345
    | exact resolve eq345 eq26476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq26488 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X1 (σ (M.op x x))))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq346 y X0 X1
       have i₂ := eq26476
       grind)
    | exact superpose eq26476 eq346
    | exact resolve eq346 eq26476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq26504 : (σ y) = (M.op (σ y) (σ (M.op (M.op (M.op x x) (M.op x x)) (M.op (M.op x x) (M.op x x))))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq667 y
       have i₂ := eq26476
       grind)
    | exact superpose eq26476 eq667
    | exact resolve eq667 eq26476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26576 : ∀ X0 X1 : G, y = (M.op y (M.op X0 (M.op X1 (M.op x x)))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq6130 y X1 y X0
       have i₂ := eq26476
       grind)
    | exact superpose eq26476 eq6130
    | exact resolve eq6130 eq26476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26622 : ∀ X0 X1 X2 : G, y = (M.op y (M.op X2 (M.op X0 (M.op X1 x)))) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26576 X2 (M.op X0 (M.op X1 x))
       have i₂ := eq6131 x X0 X1 x
       grind)
    | exact superpose eq6131 eq26576
    | exact resolve eq26576 eq6131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6131 eq26576
  have eq27524 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op X0 (σ x)) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq6166 x x X0 (σ y) x
       have i₂ := eq26488 x x
       grind)
    | exact superpose eq26488 eq6166
    | exact resolve eq6166 eq26488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6166 eq26488
  have eq32666 : ∀ X0 X1 : G, (σ (σ (τ X1))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (M.op (τ X0) (τ X0)))) = (σ (σ (M.op (τ X1) (τ X1)))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq10480 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq10480
    | (have j0 := eq10480 (τ X0) (τ X1)
       grind)
    | exact resolve eq10480 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq10480
  have eq32740 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X1))) ∨ (σ (σ (M.op (τ X0) (τ X0)))) = (σ (σ (M.op (τ X1) (τ X1)))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq32666 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq32666
    | (have j0 := eq32666 X0 X1
       grind)
    | exact resolve eq32666 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32666
  have eq32788 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (M.op (τ X0) (τ X0)))) = (σ (σ (M.op (τ X1) (τ X1)))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq32740 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq32740
    | (have j0 := eq32740 X0 X1
       grind)
    | exact resolve eq32740 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32740
  have eq32821 : ∀ X0 X1 : G, (σ (σ (M.op (τ X0) (τ X0)))) = (σ (σ (τ (M.op X1 X1)))) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq32788 X0 X1
       have i₂ := eq359 X1
       grind)
    | exact superpose eq359 eq32788
    | (have j0 := eq32788 X0 X1
       grind)
    | exact resolve eq32788 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32788
  have eq32849 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (σ (M.op (τ X0) (τ X0)))) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq32821 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq32821
    | (have j0 := eq32821 X0 X1
       grind)
    | exact resolve eq32821 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32821
  have eq32872 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (σ (τ (M.op X0 X0)))) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq32849 X0 X1
       have i₂ := eq359 X0
       grind)
    | exact superpose eq359 eq32849
    | (have j0 := eq32849 X0 X1
       grind)
    | exact resolve eq32849 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359 eq32849
  have eq32894 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq32872 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq32872
    | (have j0 := eq32872 X0 X1
       grind)
    | exact resolve eq32872 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32872
  have eq32911 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (σ (τ X0))) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32894 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32894
    | (have j0 := eq32894 X0 X1
       grind)
    | exact resolve eq32894 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32894
  have eq32920 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32911 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32911
    | (have j0 := eq32911 X0 X1
       grind)
    | exact resolve eq32911 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32911
  have eq33913 : (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq26479 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26479
  have eq33931 : y = (M.op x y) ∨ (k x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq26480 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26480
  have eq33932 : (k x y) = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq33931
  have eq41911 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ X0)) = (σ (k X0 y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4172 y X0
       have i₂ := eq26476
       grind)
    | exact superpose eq26476 eq4172
    | (have j0 := eq4172 y X0
       grind)
    | exact resolve eq4172 eq26476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41923 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ X0) (σ y)) = (σ (k y X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4172 X0 y
       have i₂ := eq26476
       grind)
    | exact superpose eq26476 eq4172
    | (have j0 := eq4172 X0 y
       grind)
    | exact resolve eq4172 eq26476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4172
  have eq547896 : (σ (k x y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq41911 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41911
  have eq547899 : (M.op (σ y) (σ x)) = (σ (M.op y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33932 eq547896
    | exact resolve eq547896 eq33932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547896
  have eq548003 : (σ (M.op y x)) = (M.op (σ (M.op y x)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5431 (σ x) (σ y)
       have i₂ := eq547899
       grind)
    | exact superpose eq547899 eq5431
    | exact resolve eq5431 eq547899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547899
  have eq552278 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq41923 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41923
  have eq552317 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq552278
       have i₂ := eq33913
       grind)
    | exact superpose eq33913 eq552278
    | exact resolve eq552278 eq33913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552278
  have eq552692 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq552317
  have eq552693 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq552692
       have r₂ := eq16
       grind)
    | exact resolve eq552692 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552692
  have eq552698 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq27524 (σ y)
       have i₂ := eq552693
       grind)
    | exact superpose eq552693 eq27524
    | exact resolve eq27524 eq552693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552734 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq552693
       grind)
    | exact superpose eq552693 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq552693
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq552693
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq552693
       grind)
    | exact resolve eq12 eq552693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552739 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq5431 (σ x) (σ y)
       have i₂ := eq552693
       grind)
    | exact superpose eq552693 eq5431
    | exact resolve eq5431 eq552693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552693
  have eq552767 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq552734
  have eq552782 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq552698
  have eq552789 : (σ x) = (σ (M.op x x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq552739
       have i₂ := eq307 x
       grind)
    | exact superpose eq307 eq552739
    | exact resolve eq552739 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552739
  have eq552794 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq552767
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq552767
    | exact resolve eq552767 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552767
  have eq552801 : (σ (M.op x x)) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq552794
       have i₂ := eq307 x
       grind)
    | exact superpose eq307 eq552794
    | exact resolve eq552794 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552794
  have eq552803 : (σ (M.op x y)) = (σ (M.op x x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq33913 eq552801
    | exact resolve eq552801 eq33913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33913 eq552801
  have eq552920 : (M.op x x) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq552789
       grind)
    | exact superpose eq552789 eq10
    | exact resolve eq10 eq552789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552789
  have eq553452 : y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq552920
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq552920
    | exact resolve eq552920 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552920
  have eq554031 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq552782
       grind)
    | exact superpose eq552782 eq16
    | exact resolve eq16 eq552782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552782
  have eq554305 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq553452 eq552803
    | exact resolve eq552803 eq553452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552803 eq553452
  have eq554306 : y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq554305
       have r₂ := eq554031
       grind)
    | exact resolve eq554305 eq554031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554031 eq554305
  have eq554307 : y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq554306 eq33932
    | exact resolve eq33932 eq554306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33932
  have eq554311 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq554306 eq548003
    | exact resolve eq548003 eq554306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548003
  have eq554362 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq554311
       have i₂ := eq307 x
       grind)
    | exact superpose eq307 eq554311
    | exact resolve eq554311 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554311
  have eq572676 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq554362
       grind)
    | exact superpose eq554362 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq554362
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq554362
       grind)
    | exact resolve eq12 eq554362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554362
  have eq572709 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ y = (M.op x y) := by grind
  clear eq572676
  have eq572743 : (M.op (σ y) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq572709
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq572709
    | exact resolve eq572709 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572709
  have eq572774 : (σ (M.op y y)) = (σ (k x y)) ∨ (σ x) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq572743
       have i₂ := eq307 y
       grind)
    | exact superpose eq307 eq572743
    | exact resolve eq572743 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572743
  have eq572780 : (σ (M.op x x)) = (σ (k x y)) ∨ (σ x) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26476 eq572774
    | exact resolve eq572774 eq26476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572774
  have eq572784 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq554307 eq572780
    | exact resolve eq572780 eq554307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554307 eq572780
  have eq572785 : (σ x) = (σ (M.op x x)) ∨ y = (M.op x y) := by grind
  clear eq572784
  have eq572786 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op (M.op X0 (σ x)) (M.op X1 (σ y))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq572785 eq26486
    | exact resolve eq26486 eq572785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26486
  have eq572787 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq572785 eq26487
    | exact resolve eq26487 eq572785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26487
  have eq572908 : (M.op x x) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq572785
       grind)
    | exact superpose eq572785 eq10
    | exact resolve eq10 eq572785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572785
  have eq573430 : y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq572908
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq572908
    | exact resolve eq572908 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572908
  have eq573486 : y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq573430 eq26476
    | exact resolve eq26476 eq573430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26476
  have eq573503 : (σ y) = (M.op (σ y) (σ (M.op (M.op x x) (M.op x x)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq573430 eq26504
    | exact resolve eq26504 eq573430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26504
  have eq573650 : (σ y) = (M.op (σ y) (σ (M.op x x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq573430 eq573503
    | exact resolve eq573503 eq573430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573503
  have eq573657 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq573430 eq573650
    | exact resolve eq573650 eq573430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573650
  have eq574731 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq572787
       grind)
    | exact superpose eq572787 eq16
    | exact resolve eq16 eq572787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572787
  have eq575230 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq27524 (σ y)
       have i₂ := eq573657
       grind)
    | exact superpose eq573657 eq27524
    | exact resolve eq27524 eq573657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27524 eq573657
  have eq575306 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq575230
  have eq575341 : (σ y) = (σ (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq575306
       have i₂ := eq307 y
       grind)
    | exact superpose eq307 eq575306
    | exact resolve eq575306 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575306
  have eq575391 : y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq573486 eq575341
    | exact resolve eq575341 eq573486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573486 eq575341
  have eq603877 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op (M.op X0 (σ x)) (M.op X1 (σ x))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq575391 eq572786
    | exact resolve eq572786 eq575391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572786 eq575391
  have eq603925 : ∀ X0 X1 : G, (M.op X0 (τ (σ x))) = (M.op (M.op X0 (τ (σ x))) (M.op X1 (τ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq5457 (σ x) X1 x
       have i₂ := eq603877 (σ x) (σ x)
       grind)
    | exact superpose eq603877 eq5457
    | exact resolve eq5457 eq603877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5457 eq603877
  have eq604448 : ∀ X0 X1 : G, (M.op X0 (τ (σ x))) = (M.op (M.op X0 (τ (σ x))) (M.op X1 (τ (M.op (σ (M.op x x)) (σ (M.op x x)))))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq603925 X0 X1
       have i₂ := eq307 x
       grind)
    | exact superpose eq307 eq603925
    | exact resolve eq603925 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603925
  have eq604566 : ∀ X0 X1 : G, (M.op X0 (τ (σ x))) = (M.op (M.op X0 (τ (σ x))) (M.op X1 (τ (σ (M.op (M.op x x) (M.op x x)))))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq604448 X0 X1
       have i₂ := eq307 (M.op x x)
       grind)
    | exact superpose eq307 eq604448
    | exact resolve eq604448 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307 eq604448
  have eq604643 : ∀ X0 X1 : G, (M.op X0 (τ (σ x))) = (M.op (M.op X0 (τ (σ x))) (M.op X1 (M.op (M.op x x) (M.op x x)))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq604566 X0 X1
       have i₂ := eq10 (M.op (M.op x x) (M.op x x))
       grind)
    | exact superpose eq10 eq604566
    | exact resolve eq604566 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604566
  have eq604701 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op X0 x) (M.op X1 (M.op (M.op x x) (M.op x x)))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq604643 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq604643
    | exact resolve eq604643 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604643
  have eq604730 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op X0 x) (M.op X1 (M.op x x))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq573430 eq604701
    | exact resolve eq604701 eq573430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604701
  have eq604747 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op X0 x) (M.op X1 x)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq573430 eq604730
    | exact resolve eq604730 eq573430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604730
  have eq605369 : ∀ X0 X1 : G, x = (M.op x (M.op X1 (M.op X0 x))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq6130 x (M.op X0 x) x X1
       have i₂ := eq604747 X0 x
       grind)
    | exact superpose eq604747 eq6130
    | exact resolve eq6130 eq604747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604747
  have eq605993 : y = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26622 x x x
       have i₂ := eq605369 x x
       grind)
    | exact superpose eq605369 eq26622
    | exact resolve eq26622 eq605369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26622 eq605369
  have eq606085 : y = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq605993
  have eq606108 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq554306 eq606085
    | exact resolve eq606085 eq554306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554306 eq606085
  have eq606151 : (σ x) ≠ (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq606108 eq574731
    | exact resolve eq574731 eq606108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574731 eq606108
  have eq606284 : (σ x) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq573430 eq606151
    | exact resolve eq606151 eq573430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573430 eq606151
  have eq606285 : y = (M.op x y) := by grind
  clear eq606284
  have eq606296 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq606285
       grind)
    | exact superpose eq606285 eq16
    | exact resolve eq16 eq606285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq606362 : y ≠ y ∨ (M.op y y) = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq606285
       grind)
    | exact superpose eq606285 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq606285
       grind)
    | exact resolve eq12 eq606285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq606367 : y = (M.op y y) := by
    first
    | (have i₁ := eq5431 y x
       have i₂ := eq606285
       grind)
    | exact superpose eq606285 eq5431
    | exact resolve eq5431 eq606285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5431
  have eq606395 : (M.op y y) = (k x y) := by grind
  clear eq606362
  have eq606720 : ∀ X0 X1 : G, y = (M.op y (M.op X0 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq6130 y X1 y X0
       have i₂ := eq606367
       grind)
    | exact superpose eq606367 eq6130
    | exact resolve eq6130 eq606367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq606853 : ∀ X0 X1 : G, y = (M.op y (M.op X0 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have j0 := eq606720 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606720
  have eq606931 : y = (k x y) := by
    first
    | (have i₁ := eq606395
       have i₂ := eq606367
       grind)
    | exact superpose eq606367 eq606395
    | exact resolve eq606395 eq606367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606395
  have eq606960 : (σ y) ≠ (σ y) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32920 x y
       have i₂ := eq606931
       grind)
    | exact superpose eq606931 eq32920
    | (have j0 := eq32920 x y
       grind)
    | exact resolve eq32920 eq606931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32920 eq606931
  have eq606967 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq606960
  have eq606977 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq606967
       have i₂ := eq606367
       grind)
    | exact superpose eq606367 eq606967
    | exact resolve eq606967 eq606367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606967
  have eq606996 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq606977
       have r₂ := eq606296
       grind)
    | exact resolve eq606977 eq606296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606977
  have eq607074 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq606996
       grind)
    | exact superpose eq606996 eq10
    | exact resolve eq10 eq606996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606996
  have eq607611 : y = (M.op x x) := by
    first
    | (have i₁ := eq607074
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq607074
    | exact resolve eq607074 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607074
  have eq607675 : (σ x) = (M.op (σ x) (σ (M.op (M.op y y) (M.op y y)))) := by
    first
    | (have i₁ := eq667 x
       have i₂ := eq607611
       grind)
    | exact superpose eq607611 eq667
    | exact resolve eq667 eq607611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq607882 : ∀ X0 X1 : G, x = (M.op x (M.op X0 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq6130 x X1 x X0
       have i₂ := eq607611
       grind)
    | exact superpose eq607611 eq6130
    | exact resolve eq6130 eq607611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6130 eq607611
  have eq607973 : (σ x) = (M.op (σ x) (σ (M.op y y))) := by
    first
    | (have i₁ := eq607675
       have i₂ := eq606367
       grind)
    | exact superpose eq606367 eq607675
    | exact resolve eq607675 eq606367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607675
  have eq608000 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq607973
       have i₂ := eq606367
       grind)
    | exact superpose eq606367 eq607973
    | exact resolve eq607973 eq606367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606367 eq607973
  have eq608744 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq606296
       have i₂ := eq608000
       grind)
    | exact superpose eq608000 eq606296
    | exact resolve eq606296 eq608000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606296 eq608000
  have eq609015 : ∀ X0 : G, y = (M.op y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq606853 X0 x
       have i₂ := eq606285
       grind)
    | exact superpose eq606285 eq606853
    | exact resolve eq606853 eq606285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606853
  have eq609239 : x = (M.op x y) := by
    first
    | (have i₁ := eq607882 y x
       have i₂ := eq609015 x
       grind)
    | exact superpose eq609015 eq607882
    | exact resolve eq607882 eq609015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607882 eq609015
  have eq609349 : x = y := by
    first
    | (have i₁ := eq606285
       have i₂ := eq609239
       grind)
    | exact superpose eq609239 eq606285
    | exact resolve eq606285 eq609239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606285 eq609239
  have eq609448 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq608744
       have i₂ := eq609349
       grind)
    | exact superpose eq609349 eq608744
    | exact resolve eq608744 eq609349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608744 eq609349
  have eq609451 : False := by grind
  exact eq609451

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_pyx_pxy_pyx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  clear eq17
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
  have eq474 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq475 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq474 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq474
    | (have j0 := eq474 (σ X0) (σ X1)
       grind)
    | exact resolve eq474 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq807 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq475 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq475 X0 X1
       grind)
    | exact superpose eq475 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq475 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq475 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq475 X0 X1
       grind)
    | exact resolve eq13 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq812 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq807 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq818 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq812 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq812 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq812 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq834 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq818 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq818
    | (have j0 := eq818 X0 X1
       grind)
    | exact resolve eq818 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq835 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq834 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq849 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq835 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq835
    | exact resolve eq835 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq868 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq849 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq849
    | exact resolve eq849 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq879 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq868 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq868
    | exact resolve eq868 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq888 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq879 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq879
    | exact resolve eq879 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq893 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq835 X0 X1
       have i₂ := eq888 X0 X1
       grind)
    | exact superpose eq888 eq835
    | exact resolve eq835 eq888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835 eq888
  have eq923 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq893 x y
       grind)
    | exact superpose eq893 eq16
    | (have r₁ := eq16
       have r₂ := eq893 x y
       grind)
    | exact resolve eq16 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq948 : False := by grind
  exact eq948

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_pyx_pyy_pyx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq47 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq47 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq47 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq50 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq48 (σ X0)
       grind)
    | exact superpose eq48 eq15
    | exact resolve eq15 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq50 X0
       have i₂ := eq48 X0
       grind)
    | exact superpose eq48 eq50
    | exact resolve eq50 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq80 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq88 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (σ X0)
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq20
    | exact resolve eq20 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq118 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
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
  have eq171 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq80 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq80 X0 X1
       grind)
    | exact superpose eq80 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq80 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq80 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq80 X0 X1
       grind)
    | exact resolve eq13 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq177 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq171 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq178 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq177 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq183 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq178
    | (have j0 := eq178 X0 X1
       grind)
    | exact resolve eq178 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq184 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq183 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq213 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq12 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq88 X0
       grind)
    | exact superpose eq88 eq12
    | (have j0 := eq12 (σ (M.op X0 X0)) (σ X0)
       grind)
    | exact resolve eq12 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (M.op X0 X0) X0)) ∨ (σ X0) ≠ (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq213 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq213
    | (have j0 := eq213 X0
       grind)
    | exact resolve eq213 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq225 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k (M.op X0 X0) X0)) ∨ (σ X0) ≠ (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq216 X0
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq216
    | (have j0 := eq216 X0
       grind)
    | exact resolve eq216 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq486 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq184 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq184
    | exact resolve eq184 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq493 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k (M.op X0 X0) X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq184 (M.op X0 X0) X0
       have i₂ := eq88 X0
       grind)
    | exact superpose eq88 eq184
    | exact resolve eq184 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq494 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq184 x y
       grind)
    | exact superpose eq184 eq16
    | (have j1 := eq184 x y
       grind)
    | exact resolve eq16 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq512 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq184 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq526 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq493 X0
       have j1 := eq225 X0
       grind)
    | (have r₁ := eq493 X0
       have r₂ := eq225 X0
       grind)
    | exact resolve eq493 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225 eq493
  have eq528 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq486 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq486
    | (have j0 := eq486 X0 X1
       grind)
    | exact resolve eq486 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq486
  have eq894 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq118 x X2 X0 X1
       grind)
    | exact superpose eq118 eq9
    | exact resolve eq9 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq1004 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq894 x X1 X0
       grind)
    | exact superpose eq894 eq9
    | exact resolve eq9 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq1148 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq528 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq528
    | exact resolve eq528 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq1217 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq1148 (τ X0) X1
       grind)
    | exact superpose eq1148 eq17
    | (have j1 := eq1148 (τ X0) X1
       grind)
    | exact resolve eq17 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1148
  have eq2676 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1217 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1217
    | exact resolve eq1217 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217
  have eq2771 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2676 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2676
    | (have j0 := eq2676 X0 X1
       grind)
    | exact resolve eq2676 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2676
  have eq2886 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq494
       have i₂ := eq2771 x y
       grind)
    | exact superpose eq2771 eq494
    | (have j1 := eq2771 (σ x) (σ y)
       grind)
    | (have r₁ := eq494
       have r₂ := eq2771 x y
       grind)
    | exact resolve eq494 eq2771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq2887 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2886
  have eq2890 : y ≠ y ∨ (k x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq2887
       grind)
    | exact superpose eq2887 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq2887
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq2887
       grind)
    | exact resolve eq12 eq2887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2896 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1004 y x
       have i₂ := eq2887
       grind)
    | exact superpose eq2887 eq1004
    | exact resolve eq1004 eq2887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2887
  have eq2898 : (k x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2890
  have eq2911 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1004 (σ y) (σ x)
       have i₂ := eq2896
       grind)
    | exact superpose eq2896 eq1004
    | exact resolve eq1004 eq2896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004 eq2896
  have eq2914 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2911
       have i₂ := eq57 y
       grind)
    | exact superpose eq57 eq2911
    | exact resolve eq2911 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2911
  have eq3021 : (σ y) = (σ (k y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq526 y
       have i₂ := eq2914
       grind)
    | exact superpose eq2914 eq526
    | exact resolve eq526 eq2914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526 eq2914
  have eq3045 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3021
       have i₂ := eq48 y
       grind)
    | exact superpose eq48 eq3021
    | exact resolve eq3021 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq3021
  have eq3046 : (σ y) = (σ (M.op y y)) := by grind
  clear eq3045
  have eq6451 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq512 x y
       have i₂ := eq2898
       grind)
    | exact superpose eq2898 eq512
    | (have j0 := eq512 x y
       grind)
    | exact resolve eq512 eq2898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512 eq2898
  have eq6457 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq6451
  have eq6461 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq6457
       have r₂ := eq3046
       grind)
    | exact resolve eq6457 eq3046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6457
  have eq6654 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6461
       grind)
    | exact superpose eq6461 eq16
    | exact resolve eq16 eq6461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6664 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq6461
       grind)
    | exact superpose eq6461 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq6461
       grind)
    | exact resolve eq12 eq6461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6461
  have eq6673 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq6664
  have eq6676 : (k (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq6673
       have i₂ := eq57 y
       grind)
    | exact superpose eq57 eq6673
    | exact resolve eq6673 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq6673
  have eq6680 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq6676
       have i₂ := eq3046
       grind)
    | exact superpose eq3046 eq6676
    | exact resolve eq6676 eq3046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3046 eq6676
  have eq6681 : (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq6680
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq6680
    | exact resolve eq6680 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6680
  have eq6866 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2771 x y
       have i₂ := eq6681
       grind)
    | exact superpose eq6681 eq2771
    | (have j0 := eq2771 x y
       grind)
    | exact resolve eq2771 eq6681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2771 eq6681
  have eq6939 : y = (M.op x y) := by
    first
    | (have r₁ := eq6866
       have r₂ := eq6654
       grind)
    | exact resolve eq6866 eq6654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6866
  have eq7160 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq6654
       have i₂ := eq6939
       grind)
    | exact superpose eq6939 eq6654
    | exact resolve eq6654 eq6939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6654 eq6939
  have eq7184 : False := by grind
  exact eq7184

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_pyy_x_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
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
  clear eq17
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
  have eq61 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
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
  have eq62 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
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
  have eq65 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X0 X0))) ≠ X0 ∨ (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 (M.op X0 X0))) (M.op X1 (M.op X2 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 X0) X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 (M.op X2 (M.op X0 X0))) = X0 ∨ (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       grind)
    | (have r₁ := eq13 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq13 (M.op X0 X0) X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq13
    | (have j0 := eq13 X0 X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq62 X0
       grind)
    | exact resolve eq13 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq69 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq68 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq70 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 ∨ (M.op X1 (M.op X2 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq67 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq71 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq69 X0
       have j1 := eq66 X0
       grind)
    | (have r₁ := eq69 X0
       have r₂ := eq66 X0
       grind)
    | exact resolve eq69 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq69
  have eq72 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq71 (τ X0)
       grind)
    | exact superpose eq71 eq18
    | exact resolve eq18 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq61 X1 X0 X3
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq232 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq14
    | (have j0 := eq14 (τ X0) (τ X1)
       grind)
    | exact resolve eq14 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2362 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq231 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq231
    | (have j0 := eq231 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq231 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2363 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ (M.op X1 (M.op X2 (M.op X0 X0))))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X1 (M.op X2 (M.op X0 X0))))) ∨ (σ (M.op X1 (M.op X2 (M.op X0 X0)))) = (M.op (σ X0) (σ (M.op X1 (M.op X2 (M.op X0 X0))))) ∨ (M.op X1 (M.op X2 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq231 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have i₂ := eq70 X0 X1 X2
       grind)
    | exact superpose eq70 eq231
    | (have j0 := eq231 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have j1 := eq70 X0 X1 X2
       grind)
    | exact resolve eq231 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2365 : ∀ X0 X1 : G, (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq231 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq231
    | (have j0 := eq231 (σ X0) (σ X1)
       grind)
    | exact resolve eq231 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2394 : ∀ X0 X1 X2 : G, (σ (k (k X0 X1) X2)) = (k (M.op (σ X0) (σ X1)) (σ X2)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 X1) X2
       have i₂ := eq231 X0 X1
       grind)
    | exact superpose eq231 eq15
    | (have j1 := eq231 X0 X1
       grind)
    | exact resolve eq15 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq2450 : ∀ X0 X1 X2 : G, (σ (M.op X1 (M.op X2 (M.op X0 X0)))) = (M.op (σ X0) (σ (M.op X1 (M.op X2 (M.op X0 X0))))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X1 (M.op X2 (M.op X0 X0))))) ∨ (M.op X1 (M.op X2 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq2363 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2363
  have eq2837 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq72 x
       have i₂ := eq239 (τ x) x
       grind)
    | exact superpose eq239 eq72
    | (have j1 := eq239 (τ X0) X0
       grind)
    | exact resolve eq72 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq239
  have eq2902 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq2837 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2837
  have eq2908 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2902 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2902
    | (have j0 := eq2902 X0
       grind)
    | exact resolve eq2902 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2902
  have eq2935 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq22 (k (σ X0) (σ X0)) X0
       have i₂ := eq2908 (σ X0)
       grind)
    | exact superpose eq2908 eq22
    | (have j1 := eq2908 (σ X0)
       grind)
    | exact resolve eq22 eq2908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2908
  have eq2986 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2935 x
       have i₂ := eq22 (σ x) x
       grind)
    | exact superpose eq22 eq2935
    | (have j0 := eq2935 X0
       grind)
    | exact resolve eq2935 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2935
  have eq3026 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2986 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2986
    | (have j0 := eq2986 X0
       grind)
    | exact resolve eq2986 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2986
  have eq3062 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3026 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3026
    | (have j0 := eq3026 X0
       grind)
    | exact resolve eq3026 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3026
  have eq3136 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq22 (k (σ X0) (σ X0)) X0
       have i₂ := eq3062 (σ X0)
       grind)
    | exact superpose eq3062 eq22
    | (have j1 := eq3062 (σ X0)
       grind)
    | exact resolve eq22 eq3062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3062
  have eq3187 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3136 x
       have i₂ := eq22 (σ x) x
       grind)
    | exact superpose eq22 eq3136
    | (have j0 := eq3136 X0
       grind)
    | exact resolve eq3136 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3136
  have eq3227 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3187 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3187
    | (have j0 := eq3187 X0
       grind)
    | exact resolve eq3187 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3187
  have eq13750 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq79 x X2 X0 X1
       grind)
    | exact superpose eq79 eq9
    | exact resolve eq9 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq13786 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13750 X0 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq13750 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq13750 eq13750
    | exact resolve eq13750 eq13750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13796 : ∀ X0 X2 : G, (M.op X2 X0) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X2 X0) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq65 (M.op x X2) X2 X0
       have i₂ := eq13750 X0 x X2
       grind)
    | exact superpose eq13750 eq65
    | exact resolve eq65 eq13750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq13797 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq70 (M.op X1 x) x X0
       have i₂ := eq13750 X0 X1 x
       grind)
    | exact superpose eq13750 eq70
    | exact resolve eq70 eq13750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq13804 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X2 X0
       have i₂ := eq13750 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq13750 eq9
    | exact resolve eq9 eq13750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14086 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13750 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) X1 X2
       have i₂ := eq13804 (M.op X1 X2) X0 (M.op X1 X2)
       grind)
    | exact superpose eq13804 eq13750
    | exact resolve eq13750 eq13804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13750 eq13804
  have eq14157 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 (M.op X0 (M.op X1 X2)) X2 X2
       have i₂ := eq14086 X0 X1 X2
       grind)
    | exact superpose eq14086 eq61
    | exact resolve eq61 eq14086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq14158 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 X0)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 (M.op X2 X0)) X3 X0
       have i₂ := eq14086 X1 X2 X0
       grind)
    | exact superpose eq14086 eq9
    | exact resolve eq9 eq14086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14086
  have eq35764 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq71 (σ X0)
       have i₂ := eq2394 X0 X0 X0
       grind)
    | exact superpose eq2394 eq71
    | (have j1 := eq2394 X0 X0 x
       grind)
    | exact resolve eq71 eq2394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq2394
  have eq35787 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq35764 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35764
  have eq35808 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq3227 eq35787
    | (have j0 := eq35787 X0
       have j1 := eq3227 X0
       grind)
    | exact resolve eq35787 eq3227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3227 eq35787
  have eq35917 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq35808 (τ X0)
       grind)
    | exact superpose eq35808 eq18
    | (have j1 := eq35808 (τ X0)
       grind)
    | exact resolve eq18 eq35808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq35808
  have eq35998 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq35917 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq35917
    | (have j0 := eq35917 X0
       grind)
    | exact resolve eq35917 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35917
  have eq36041 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq35998 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq35998
    | (have j0 := eq35998 X0
       grind)
    | exact resolve eq35998 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35998
  have eq36074 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq36041 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq36041 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq36041 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36041
  have eq36205 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq36074 (σ X0)
       grind)
    | exact superpose eq36074 eq15
    | exact resolve eq15 eq36074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36265 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36205 X0
       have i₂ := eq36074 X0
       grind)
    | exact superpose eq36074 eq36205
    | exact resolve eq36205 eq36074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36074 eq36205
  have eq36474 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13786 (σ X0) (σ X0)
       have i₂ := eq36265 X0
       grind)
    | exact superpose eq36265 eq13786
    | exact resolve eq13786 eq36265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36479 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op X0 X0))) = (M.op (M.op X1 (σ (M.op X0 X0))) (M.op X2 (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14158 (σ X0) X1 (σ X0) x
       have i₂ := eq36265 X0
       grind)
    | exact superpose eq36265 eq14158
    | exact resolve eq14158 eq36265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14158
  have eq37765 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq36479 X0 (σ (M.op X0 X0)) x
       have i₂ := eq36265 (M.op X0 X0)
       grind)
    | exact superpose eq36265 eq36479
    | exact resolve eq36479 eq36265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37959 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq2365 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2365
  have eq38470 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2362 x y
       grind)
    | exact superpose eq2362 eq16
    | (have j1 := eq2362 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2362 x y
       grind)
    | exact resolve eq16 eq2362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2362
  have eq38547 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq38470
  have eq40135 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ (M.op X1 (M.op X2 (M.op X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X1 (M.op X2 (M.op X0 X0))))) ∨ (M.op X1 (M.op X2 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq2450 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2450
  have eq44788 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38547
       grind)
    | exact superpose eq38547 eq16
    | exact resolve eq16 eq38547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44796 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq38547
       grind)
    | exact superpose eq38547 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq38547
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq38547
       grind)
    | exact resolve eq12 eq38547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44797 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13786 (σ y) (σ x)
       have i₂ := eq38547
       grind)
    | exact superpose eq38547 eq13786
    | exact resolve eq13786 eq38547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44812 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  have eq44814 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq44796
  have eq44816 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44797
       have i₂ := eq36265 y
       grind)
    | exact superpose eq36265 eq44797
    | exact resolve eq44797 eq36265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44797
  have eq44817 : (σ (M.op y y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44814
       have i₂ := eq36265 y
       grind)
    | exact superpose eq36265 eq44814
    | exact resolve eq44814 eq36265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44814
  have eq44818 : (σ (M.op y y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44817
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq44817
    | exact resolve eq44817 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44817
  have eq44819 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14 eq44818
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq44818 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44818
  have eq52713 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq44816
       grind)
    | exact superpose eq44816 eq16
    | exact resolve eq16 eq44816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52728 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13797 (σ y) (σ x)
       have i₂ := eq44816
       grind)
    | exact superpose eq44816 eq13797
    | (have j0 := eq13797 y x
       grind)
    | exact resolve eq13797 eq44816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44816
  have eq52745 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq52728
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq52728
    | exact resolve eq52728 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52728
  have eq52750 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14 eq52745
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq52745 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52745
  have eq52755 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq52750
       have r₂ := eq52713
       grind)
    | exact resolve eq52750 eq52713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52713 eq52750
  have eq53149 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq52755
       grind)
    | exact superpose eq52755 eq10
    | exact resolve eq10 eq52755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52755
  have eq53332 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq53149
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq53149
    | exact resolve eq53149 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53149
  have eq53402 : ∀ X0 : G, (σ (M.op y y)) = (M.op (σ (M.op y y)) (M.op X0 (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq37765 y x
       have i₂ := eq53332
       grind)
    | exact superpose eq53332 eq37765
    | exact resolve eq37765 eq53332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37765
  have eq53447 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq53332 eq53402
    | exact resolve eq53402 eq53332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53332 eq53402
  have eq61985 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq53447 (σ x)
       have i₂ := eq38547
       grind)
    | exact superpose eq38547 eq53447
    | exact resolve eq53447 eq38547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38547 eq53447
  have eq62031 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq61985
  have eq62038 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq62031
       have r₂ := eq44812
       grind)
    | exact resolve eq62031 eq44812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44812 eq62031
  have eq62042 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq62038
       have i₂ := eq36265 y
       grind)
    | exact superpose eq36265 eq62038
    | exact resolve eq62038 eq36265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62038
  have eq63413 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq232 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq64153 : ∀ X0 X1 : G, (σ (σ (τ X0))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq37959 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq37959
    | (have j0 := eq37959 (τ X0) (τ X1)
       grind)
    | exact resolve eq37959 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq37959
  have eq64253 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X0))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq64153 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq64153
    | (have j0 := eq64153 X0 X1
       grind)
    | exact resolve eq64153 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64153
  have eq64295 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq64253 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq64253
    | (have j0 := eq64253 X0 X1
       grind)
    | exact resolve eq64253 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64253
  have eq64329 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq64295 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq64295
    | (have j0 := eq64295 X0 X1
       grind)
    | exact resolve eq64295 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64295
  have eq64355 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq64329 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq64329
    | (have j0 := eq64329 X0 X1
       grind)
    | exact resolve eq64329 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64329
  have eq64376 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (σ (τ X0))) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq64355 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq64355
    | (have j0 := eq64355 X0 X1
       grind)
    | exact resolve eq64355 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64355
  have eq64397 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq64376 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq64376
    | (have j0 := eq64376 X0 X1
       grind)
    | exact resolve eq64376 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64376
  have eq64726 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ X1)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) ∨ (τ (σ X1)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq63413 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq63413
    | (have j0 := eq63413 (σ X0) (σ X1)
       grind)
    | exact resolve eq63413 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63413
  have eq64817 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) ∨ (τ (σ X1)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq64726 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq64726
    | (have j0 := eq64726 X0 X1
       grind)
    | exact resolve eq64726 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64726
  have eq64864 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) ∨ (τ (σ X1)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq64817 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq64817
    | (have j0 := eq64817 X0 X1
       grind)
    | exact resolve eq64817 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64817
  have eq64901 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq64864 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq64864
    | (have j0 := eq64864 X0 X1
       grind)
    | exact resolve eq64864 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64864
  have eq64937 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq64901 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq64901
    | (have j0 := eq64901 X0 X1
       grind)
    | exact resolve eq64901 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64901
  have eq64966 : ∀ X0 X1 : G, (M.op (τ (σ X0)) X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq64937 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq64937
    | (have j0 := eq64937 X0 X1
       grind)
    | exact resolve eq64937 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64937
  have eq64989 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq64966 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq64966
    | (have j0 := eq64966 X0 X1
       grind)
    | exact resolve eq64966 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64966
  have eq65043 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq64989 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq64989
    | (have j0 := eq64989 (σ X0) (σ X1)
       grind)
    | exact resolve eq64989 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64989
  have eq74559 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq62042 eq44819
    | exact resolve eq44819 eq62042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44819 eq62042
  have eq74560 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq74559
       have r₂ := eq44788
       grind)
    | exact resolve eq74559 eq44788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44788 eq74559
  have eq74562 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq74560
       grind)
    | exact superpose eq74560 eq16
    | exact resolve eq16 eq74560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74582 : (σ x) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13796 (σ y) (σ x)
       have i₂ := eq74560
       grind)
    | exact superpose eq74560 eq13796
    | (have r₁ := eq13796 y x
       have r₂ := eq74560
       grind)
    | exact resolve eq13796 eq74560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13796
  have eq74583 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13797 (σ y) (σ x)
       have i₂ := eq74560
       grind)
    | exact superpose eq74560 eq13797
    | (have j0 := eq13797 y x
       grind)
    | exact resolve eq13797 eq74560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74608 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq74583
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq74583
    | exact resolve eq74583 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74583
  have eq74609 : (σ (M.op y y)) = (k (σ x) (σ y)) ∨ (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq74582
       have i₂ := eq36265 y
       grind)
    | exact superpose eq36265 eq74582
    | exact resolve eq74582 eq36265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74582
  have eq74614 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14 eq74608
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq74608 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74608
  have eq74615 : (σ (M.op y y)) = (σ (k x y)) ∨ (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq74609
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq74609
    | exact resolve eq74609 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74609
  have eq74619 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq74614
       have r₂ := eq74562
       grind)
    | exact resolve eq74614 eq74562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74562 eq74614
  have eq74620 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14 eq74615
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq74615 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74615
  have eq74623 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq74620
       have r₂ := eq74619
       grind)
    | exact resolve eq74620 eq74619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74620
  have eq74629 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq74619 eq74560
    | exact resolve eq74560 eq74619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74560
  have eq74654 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq74629
       have i₂ := eq36265 x
       grind)
    | exact superpose eq36265 eq74629
    | exact resolve eq74629 eq36265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74629
  have eq75093 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq74654
       grind)
    | exact superpose eq74654 eq10
    | exact resolve eq10 eq74654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74654
  have eq75313 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq75093
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq75093
    | exact resolve eq75093 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75093
  have eq75649 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq36474 y
       have i₂ := eq74623
       grind)
    | exact superpose eq74623 eq36474
    | exact resolve eq36474 eq74623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36474
  have eq75681 : (M.op y y) = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq74623
       grind)
    | exact superpose eq74623 eq10
    | exact resolve eq10 eq74623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74623
  have eq75901 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq75681
       have i₂ := eq10 (M.op x y)
       grind)
    | exact superpose eq10 eq75681
    | exact resolve eq75681 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75681
  have eq75933 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq74619 eq75649
    | exact resolve eq75649 eq74619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74619 eq75649
  have eq77780 : ∀ X0 : G, (M.op X0 (σ (M.op x x))) = (M.op (M.op X0 (σ (M.op x x))) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq36479 x X0 (σ (M.op x y))
       have i₂ := eq75933
       grind)
    | exact superpose eq75933 eq36479
    | exact resolve eq36479 eq75933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36479
  have eq77828 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op X0 (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq75313 eq77780
    | exact resolve eq77780 eq75313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75313 eq77780
  have eq84457 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq77828 (σ (M.op x y))
       have i₂ := eq75933
       grind)
    | exact superpose eq75933 eq77828
    | exact resolve eq77828 eq75933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75933 eq77828
  have eq84503 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq84457
  have eq84510 : (σ (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq84503
       have i₂ := eq36265 (M.op x y)
       grind)
    | exact superpose eq36265 eq84503
    | exact resolve eq84503 eq36265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84503
  have eq84546 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op (M.op x y) (M.op x y))
       have i₂ := eq84510
       grind)
    | exact superpose eq84510 eq10
    | exact resolve eq10 eq84510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84510
  have eq84766 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq84546
       have i₂ := eq10 (M.op x y)
       grind)
    | exact superpose eq10 eq84546
    | exact resolve eq84546 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84546
  have eq84803 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14157 y (M.op x y) x X0
       have i₂ := eq84766
       grind)
    | exact superpose eq84766 eq14157
    | exact resolve eq14157 eq84766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84766
  have eq85017 : y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14157 y x x y
       have i₂ := eq84803 x
       grind)
    | exact superpose eq84803 eq14157
    | exact resolve eq14157 eq84803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84803
  have eq85078 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq85017 eq75901
    | exact resolve eq75901 eq85017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75901 eq85017
  have eq85232 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq85078
  have eq85430 : y ≠ y ∨ (k x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq85232
       grind)
    | exact superpose eq85232 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq85232
       grind)
    | exact resolve eq12 eq85232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85432 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13786 y x
       have i₂ := eq85232
       grind)
    | exact superpose eq85232 eq13786
    | exact resolve eq13786 eq85232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85454 : (k x y) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq85430
  have eq85712 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq85432 eq85454
    | exact resolve eq85454 eq85432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85432 eq85454
  have eq85727 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq65043 x y
       have i₂ := eq85712
       grind)
    | exact superpose eq85712 eq65043
    | (have j0 := eq65043 x y
       grind)
    | exact resolve eq65043 eq85712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65043
  have eq85733 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq85727
  have eq88900 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq85733
       grind)
    | exact superpose eq85733 eq16
    | exact resolve eq16 eq85733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85733
  have eq88985 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq85232 eq88900
    | exact resolve eq88900 eq85232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88900
  have eq88986 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq88985
  have eq89290 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq88986
       grind)
    | exact superpose eq88986 eq16
    | exact resolve eq16 eq88986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89318 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13797 (σ y) (σ x)
       have i₂ := eq88986
       grind)
    | exact superpose eq88986 eq13797
    | exact resolve eq13797 eq88986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88986
  have eq89346 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq89318
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq89318
    | exact resolve eq89318 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89318
  have eq89367 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq85232 eq89290
    | exact resolve eq89290 eq85232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85232 eq89290
  have eq89368 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq85712 eq89346
    | exact resolve eq89346 eq85712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85712 eq89346
  have eq89369 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq89368
  have eq89382 : x = (M.op x y) := by
    first
    | (have r₁ := eq89369
       have r₂ := eq89367
       grind)
    | exact resolve eq89369 eq89367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89367 eq89369
  have eq89394 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq89382
       grind)
    | exact superpose eq89382 eq16
    | exact resolve eq16 eq89382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89410 : x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq13797 y x
       have i₂ := eq89382
       grind)
    | exact superpose eq89382 eq13797
    | exact resolve eq13797 eq89382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13797
  have eq89416 : ∀ X0 X1 : G, y = (M.op y (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq14157 y X1 x X0
       have i₂ := eq89382
       grind)
    | exact superpose eq89382 eq14157
    | exact resolve eq14157 eq89382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14157
  have eq89472 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq64397 x y
       have i₂ := eq89410
       grind)
    | exact superpose eq89410 eq64397
    | (have j0 := eq64397 x y
       grind)
    | exact resolve eq64397 eq89410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64397
  have eq89477 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq89472
  have eq89486 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq89477
       have r₂ := eq89394
       grind)
    | exact resolve eq89477 eq89394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89477
  have eq89495 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq40135 x y x
       have i₂ := eq89416 x x
       grind)
    | exact superpose eq89416 eq40135
    | exact resolve eq40135 eq89416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40135 eq89416
  have eq89549 : (σ x) ≠ (σ y) ∨ x = y := by
    first
    | (have r₁ := eq89495
       have r₂ := eq89394
       grind)
    | exact resolve eq89495 eq89394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89495
  have eq89918 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq89486
       grind)
    | exact superpose eq89486 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq89486
       grind)
    | exact resolve eq12 eq89486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89920 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq13786 (σ y) (σ x)
       have i₂ := eq89486
       grind)
    | exact superpose eq89486 eq13786
    | exact resolve eq13786 eq89486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13786 eq89486
  have eq89941 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq89918
  have eq89943 : (σ y) = (σ (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq89920
       have i₂ := eq36265 y
       grind)
    | exact superpose eq36265 eq89920
    | exact resolve eq89920 eq36265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89920
  have eq89945 : (σ (M.op y y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq89941
       have i₂ := eq36265 y
       grind)
    | exact superpose eq36265 eq89941
    | exact resolve eq89941 eq36265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89941
  have eq89948 : (σ (M.op y y)) = (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq89945
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq89945
    | exact resolve eq89945 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89945
  have eq89949 : (σ x) = (σ (M.op y y)) ∨ x = y := by
    first
    | exact superpose eq89410 eq89948
    | exact resolve eq89948 eq89410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89410 eq89948
  have eq89982 : (τ (σ y)) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq89943
       grind)
    | exact superpose eq89943 eq10
    | exact resolve eq10 eq89943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89943
  have eq90202 : y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq89982
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq89982
    | exact resolve eq89982 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89982
  have eq90406 : (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq90202 eq89949
    | exact resolve eq89949 eq90202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89949 eq90202
  have eq90407 : x = y := by
    first
    | (have r₁ := eq90406
       have r₂ := eq89549
       grind)
    | exact resolve eq90406 eq89549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89549 eq90406
  have eq90408 : x = (M.op x x) := by
    first
    | (have i₁ := eq89382
       have i₂ := eq90407
       grind)
    | exact superpose eq90407 eq89382
    | exact resolve eq89382 eq90407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89382
  have eq90409 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq89394
       have i₂ := eq90407
       grind)
    | exact superpose eq90407 eq89394
    | exact resolve eq89394 eq90407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89394 eq90407
  have eq90413 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq90409
       have i₂ := eq36265 x
       grind)
    | exact superpose eq36265 eq90409
    | exact resolve eq90409 eq36265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36265 eq90409
  have eq90596 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq90413
       have i₂ := eq90408
       grind)
    | exact superpose eq90408 eq90413
    | exact resolve eq90413 eq90408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90408 eq90413
  have eq90597 : False := by grind
  exact eq90597

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,Y) else if m(Y,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pyy_x_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
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
  have eq28 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X0 X0))) ≠ X0 ∨ (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 (M.op X0 X0))) (M.op X1 (M.op X2 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 X0) X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
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
  have eq46 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    grind
  have eq49 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq21 (τ X0)
       grind)
    | exact superpose eq21 eq46
    | (have j0 := eq46 X0
       grind)
    | exact resolve eq46 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq75 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq27
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq27 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq78 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (M.op (τ X0) X1) = X1 := by
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
  have eq85 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
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
  have eq95 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq76 x y
       grind)
    | exact superpose eq76 eq16
    | (have j1 := eq76 x y
       grind)
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq21 (σ x)
       have i₂ := eq76 x x
       grind)
    | exact superpose eq76 eq21
    | (have j1 := eq76 X0 X0
       grind)
    | exact resolve eq21 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq102 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq76 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq76 X0 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq12 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq99 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq111 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq102 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq102 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq102 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq115 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq111 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq111
    | (have j0 := eq111 X0 X1
       grind)
    | exact resolve eq111 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq191 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (M.op (σ X0) X1) (σ X2)) ∨ (σ X0) = (M.op X1 X1) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 X1 X2
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq34
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq34 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq266 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (M.op (σ (k (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq107 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq107
    | exact resolve eq107 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq277 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (k (σ (τ X0)) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq266 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq266
    | (have j0 := eq266 X0
       grind)
    | exact resolve eq266 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq281 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq277 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq277
    | (have j0 := eq277 X0
       grind)
    | exact resolve eq277 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq331 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq78 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq78
    | exact resolve eq78 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq363 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq331 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq331
    | (have j0 := eq331 X0 X1
       grind)
    | exact resolve eq331 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq553 : ∀ X0 : G, (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) = (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq27 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0
       have i₂ := eq49 (σ X0)
       grind)
    | exact superpose eq49 eq27
    | (have j1 := eq49 (σ X0)
       grind)
    | exact resolve eq27 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq560 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ X0))) = (k (M.op (τ (σ X0)) (τ (σ X0))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq553 X0
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq553
    | (have j0 := eq553 X0
       grind)
    | exact resolve eq553 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq582 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq560 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq560
    | (have j0 := eq560 X0
       grind)
    | exact resolve eq560 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq596 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq582 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq582
    | (have j0 := eq582 X0
       grind)
    | exact resolve eq582 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq603 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq596 X0
       have j1 := eq29 X0
       grind)
    | (have r₁ := eq596 X0
       have r₂ := eq29 X0
       grind)
    | exact resolve eq596 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq596
  have eq608 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq603 (σ x)
       have i₂ := eq76 x x
       grind)
    | exact superpose eq76 eq603
    | (have j1 := eq76 X0 X0
       grind)
    | exact resolve eq603 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq613 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq27 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq603 (σ X0)
       grind)
    | exact superpose eq603 eq27
    | exact resolve eq27 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq614 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq603 (τ X0)
       grind)
    | exact superpose eq603 eq19
    | exact resolve eq19 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq617 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq608 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq622 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq617 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq617
    | (have j0 := eq617 X0
       grind)
    | exact resolve eq617 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq631 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq104
    | (have j0 := eq104 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq104 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq639 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq104 (τ X0) (τ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq104
    | (have j0 := eq104 (τ X0) (τ X1)
       grind)
    | exact resolve eq104 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq646 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq639 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq639
    | (have j0 := eq639 X0 X1
       grind)
    | exact resolve eq639 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq651 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq646 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq646
    | (have j0 := eq646 X0 X1
       grind)
    | exact resolve eq646 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq654 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq651 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq651
    | (have j0 := eq651 X0 X1
       grind)
    | exact resolve eq651 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq656 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq654 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq654
    | (have j0 := eq654 X0 X1
       grind)
    | exact resolve eq654 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq657 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq656 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq656
    | (have j0 := eq656 X0 X1
       grind)
    | exact resolve eq656 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq658 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq657 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq657
    | (have j0 := eq657 X0 X1
       grind)
    | exact resolve eq657 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq896 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq85 x X2 X0 X1
       grind)
    | exact superpose eq85 eq9
    | exact resolve eq9 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq921 : ∀ X0 X2 : G, (M.op X2 X0) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X2 X0) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq28 (M.op x X2) X2 X0
       have i₂ := eq896 X0 x X2
       grind)
    | exact superpose eq896 eq28
    | exact resolve eq28 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq922 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq896 x X1 X0
       grind)
    | exact superpose eq896 eq9
    | exact resolve eq9 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq961 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq95
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq95 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq962 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq961
  have eq1059 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq115 (τ X1) (τ X0)
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq115
    | (have j0 := eq115 (τ (k X0 X1)) (τ X1)
       grind)
    | exact resolve eq115 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1077 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1059 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1059
    | (have j0 := eq1059 X0 X1
       grind)
    | exact resolve eq1059 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059
  have eq1081 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1077 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1077
    | (have j0 := eq1077 X0 X1
       grind)
    | exact resolve eq1077 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq1084 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1081 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1081
    | (have j0 := eq1081 X0 X1
       grind)
    | exact resolve eq1081 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081
  have eq1085 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1084 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1084
    | (have j0 := eq1084 X0 X1
       grind)
    | exact resolve eq1084 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1086 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1085 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1085
    | (have j0 := eq1085 X0 X1
       grind)
    | exact resolve eq1085 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085
  have eq1087 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1086 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1086
    | (have j0 := eq1086 X0 X1
       grind)
    | exact resolve eq1086 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086
  have eq1251 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1087 (τ (M.op (σ X0) (σ X0))) X0
       have i₂ := eq613 X0
       grind)
    | exact superpose eq613 eq1087
    | (have j0 := eq1087 (τ (M.op (σ X0) (σ X0))) X0
       grind)
    | exact resolve eq1087 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1258 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq1251 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251
  have eq1710 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq363 (τ X0) (τ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq363
    | (have j0 := eq363 (τ X0) (τ X1)
       grind)
    | exact resolve eq363 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1783 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1710 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1710
    | (have j0 := eq1710 X0 X1
       grind)
    | exact resolve eq1710 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1710
  have eq1930 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) (σ X0)) ∨ (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq921 (σ X0) (σ X0)
       have i₂ := eq622 X0
       grind)
    | exact superpose eq622 eq921
    | (have j1 := eq622 X0
       grind)
    | (have r₁ := eq921 (σ X0) (σ X0)
       have r₂ := eq622 X0
       grind)
    | exact resolve eq921 eq622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq1932 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq1930 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1930
  have eq1938 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq1932 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1932
    | (have j0 := eq1932 X0
       grind)
    | exact resolve eq1932 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1932
  have eq2631 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k (k X0 X0) X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1938 x
       have i₂ := eq363 x x
       grind)
    | exact superpose eq363 eq1938
    | (have j1 := eq363 X0 X0
       grind)
    | exact resolve eq1938 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363 eq1938
  have eq2688 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k (k X0 X0) X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2631 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2631
  have eq9273 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq75 (k (σ x) (σ x)) x
       have i₂ := eq281 (σ x)
       grind)
    | exact superpose eq281 eq75
    | (have j0 := eq75 (σ X0) X0
       have j1 := eq281 (σ X0)
       grind)
    | exact resolve eq75 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq281
  have eq9337 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq9273 X0
       have j1 := eq1087 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq9273 X0
       have r₂ := eq1087 (σ X0) (σ X0)
       grind)
    | exact resolve eq9273 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087 eq9273
  have eq9344 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq9337 X0
       have j1 := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq9337 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | exact resolve eq9337 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9337
  have eq9347 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9344 x
       have i₂ := eq27 (σ x) x
       grind)
    | exact superpose eq27 eq9344
    | (have j0 := eq9344 X0
       grind)
    | exact resolve eq9344 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq9344
  have eq9348 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9347 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9347
    | (have j0 := eq9347 X0
       grind)
    | exact resolve eq9347 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9347
  have eq9349 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9348 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq9348
    | (have j0 := eq9348 X0
       grind)
    | exact resolve eq9348 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9348
  have eq9368 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq115 (k X0 X0) X0
       have i₂ := eq9349 X0
       grind)
    | exact superpose eq9349 eq115
    | (have j0 := eq115 X0 X0
       have j1 := eq9349 X0
       grind)
    | exact resolve eq115 eq9349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq9381 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq9349 (τ X0)
       grind)
    | exact superpose eq9349 eq19
    | (have j1 := eq9349 (τ X0)
       grind)
    | exact resolve eq19 eq9349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9349
  have eq9398 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq9368 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9368
  have eq9417 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq9381 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq9381
    | (have j0 := eq9381 X0
       grind)
    | exact resolve eq9381 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9381
  have eq9453 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq9417 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9417
    | (have j0 := eq9417 X0
       grind)
    | exact resolve eq9417 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9417
  have eq9486 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (k (σ (τ X0)) X0) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9453 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq9453
    | (have j0 := eq9453 X0
       grind)
    | exact resolve eq9453 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9453
  have eq9518 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq9486 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9486
    | (have j0 := eq9486 X0
       grind)
    | exact resolve eq9486 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9486
  have eq9603 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq9518 (τ X0)
       grind)
    | exact superpose eq9518 eq19
    | (have j1 := eq9518 (τ X0)
       grind)
    | exact resolve eq19 eq9518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9518
  have eq9642 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq9603 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq9603
    | (have j0 := eq9603 X0
       grind)
    | exact resolve eq9603 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9603
  have eq9678 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq9642 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9642
    | (have j0 := eq9642 X0
       grind)
    | exact resolve eq9642 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9642
  have eq9710 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9678 X0
       have i₂ := eq38 X0 X0
       grind)
    | exact superpose eq38 eq9678
    | (have j0 := eq9678 X0
       grind)
    | exact resolve eq9678 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9678
  have eq10326 : ∀ X0 : G, (σ (τ (k X0 X0))) = (k (σ (τ (k X0 X0))) X0) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq614 X0
       have i₂ := eq9710 X0
       grind)
    | exact superpose eq9710 eq614
    | (have j1 := eq9710 X0
       grind)
    | exact resolve eq614 eq9710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614 eq9710
  have eq10380 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq10326 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq10326
    | (have j0 := eq10326 X0
       grind)
    | exact resolve eq10326 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10326
  have eq10381 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq10380 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10380
  have eq10553 : y ≠ y ∨ (k x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq962
       grind)
    | exact superpose eq962 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq962
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq962
       grind)
    | exact resolve eq12 eq962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq10574 : (k x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq10553
  have eq11883 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 (τ (σ X0))) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq603 (σ X0)
       have i₂ := eq191 X0 (σ X0) X0
       grind)
    | exact superpose eq191 eq603
    | (have j1 := eq191 X0 (σ X0) x
       grind)
    | exact resolve eq603 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq603
  have eq11903 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 (τ (σ X0))) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq11883 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11883
  have eq11915 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq11903 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11903
    | (have j0 := eq11903 X0
       grind)
    | exact resolve eq11903 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11903
  have eq11969 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11915 X0
       have i₂ := eq10381 X0
       grind)
    | exact superpose eq10381 eq11915
    | (have j0 := eq11915 X0
       grind)
    | exact resolve eq11915 eq10381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11915
  have eq11991 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11969 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11969
    | exact resolve eq11969 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12037 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq921 (σ X0) (σ X0)
       have i₂ := eq11969 X0
       grind)
    | exact superpose eq11969 eq921
    | (have j1 := eq11969 X0
       grind)
    | (have r₁ := eq921 (σ X0) (σ X0)
       have r₂ := eq11969 X0
       grind)
    | exact resolve eq921 eq11969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921 eq11969
  have eq12053 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq12037 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12037
  have eq12058 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12053 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq12053
    | (have j0 := eq12053 X0
       grind)
    | exact resolve eq12053 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12053
  have eq12070 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11991 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq11991
    | (have j0 := eq11991 X0
       grind)
    | exact resolve eq11991 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq11991
  have eq12073 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq12058 X0
       have j1 := eq9398 X0
       grind)
    | (have r₁ := eq12058 X0
       have r₂ := eq9398 X0
       grind)
    | exact resolve eq12058 eq9398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9398 eq12058
  have eq12080 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12070 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12070
    | (have j0 := eq12070 X0
       grind)
    | exact resolve eq12070 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12070
  have eq12083 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12080 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq12080 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq12080 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12080
  have eq12165 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0 X0
       have i₂ := eq12083 (τ X0)
       grind)
    | exact superpose eq12083 eq38
    | exact resolve eq38 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq12217 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12165 X0
       have i₂ := eq12083 X0
       grind)
    | exact superpose eq12083 eq12165
    | exact resolve eq12165 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12165
  have eq12799 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq922 (σ X0) (σ X0)
       have i₂ := eq12073 X0
       grind)
    | exact superpose eq12073 eq922
    | exact resolve eq922 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12828 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq12799 X0
       have i₂ := eq12083 X0
       grind)
    | exact superpose eq12083 eq12799
    | exact resolve eq12799 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12799
  have eq13215 : ∀ X0 : G, (σ (σ (k X0 X0))) = (M.op (σ (σ (k X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq12828 (σ X0)
       have i₂ := eq12073 X0
       grind)
    | exact superpose eq12073 eq12828
    | exact resolve eq12828 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13316 : ∀ X0 : G, (σ (σ (M.op X0 X0))) = (M.op (σ (σ (M.op X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq13215 X0
       have i₂ := eq12083 X0
       grind)
    | exact superpose eq12083 eq13215
    | exact resolve eq13215 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13215
  have eq504415 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq922 (τ X1) (τ X0)
       have i₂ := eq1783 X0 X1
       grind)
    | exact superpose eq1783 eq922
    | (have j1 := eq1783 X0 X0
       grind)
    | exact resolve eq922 eq1783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1783
  have eq504530 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq504415 X0 X1
       have i₂ := eq12217 X0
       grind)
    | exact superpose eq12217 eq504415
    | (have j0 := eq504415 X0 X1
       grind)
    | exact resolve eq504415 eq12217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504415
  have eq504840 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ X1) = (τ (M.op X0 X0)) ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq504530 X0 X1
       have i₂ := eq12217 X0
       grind)
    | exact superpose eq12217 eq504530
    | (have j0 := eq504530 X0 X1
       grind)
    | exact resolve eq504530 eq12217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12217 eq504530
  have eq505524 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (τ X1) = (τ (M.op (σ X0) (σ X0))) ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq613 X0
       have i₂ := eq504840 (σ X0) X1
       grind)
    | exact superpose eq504840 eq613
    | (have j1 := eq504840 (σ X0) X1
       grind)
    | exact resolve eq613 eq504840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613 eq504840
  have eq505874 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (τ X1) = (τ (M.op (σ X0) (σ X0))) ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq505524 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq505524
    | (have j0 := eq505524 X0 X1
       grind)
    | exact resolve eq505524 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505524
  have eq505933 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (τ X1) = (τ (M.op (σ X0) (σ X0))) ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq505874 X0 X1
       have i₂ := eq12083 X0
       grind)
    | exact superpose eq12083 eq505874
    | (have j0 := eq505874 X0 X1
       grind)
    | exact resolve eq505874 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505874
  have eq505978 : ∀ X0 X1 : G, (τ X1) = (τ (σ (k X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq505933 X0 X1
       have i₂ := eq12073 X0
       grind)
    | exact superpose eq12073 eq505933
    | (have j0 := eq505933 X0 X1
       grind)
    | exact resolve eq505933 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505933
  have eq506009 : ∀ X0 X1 : G, (τ X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq505978 X0 X1
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq505978
    | (have j0 := eq505978 X0 X1
       grind)
    | exact resolve eq505978 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505978
  have eq506029 : ∀ X0 X1 : G, (M.op X0 X0) = (τ X1) ∨ (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq506009 X0 X1
       have i₂ := eq12083 X0
       grind)
    | exact superpose eq12083 eq506009
    | (have j0 := eq506009 X0 X1
       grind)
    | exact resolve eq506009 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506009
  have eq506046 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (M.op X0 X0) = (τ X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq506029 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq506029
    | (have j0 := eq506029 X0 X1
       grind)
    | exact resolve eq506029 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506029
  have eq507420 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq506046 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq506046
    | (have j0 := eq506046 X1 X1
       grind)
    | exact resolve eq506046 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506046
  have eq508230 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq507420 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq507420
    | (have j0 := eq507420 X0 X1
       grind)
    | exact resolve eq507420 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507420
  have eq508918 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq508230 X0 X1
       grind)
    | exact superpose eq508230 eq10
    | (have j1 := eq508230 X0 X1
       grind)
    | exact resolve eq10 eq508230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq509504 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq508918 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq508918
    | (have j0 := eq508918 X1 X1
       grind)
    | exact resolve eq508918 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508918
  have eq512671 : ∀ X0 X1 : G, (τ (σ X0)) ≠ X0 ∨ (M.op X0 X0) = (τ (σ X0)) ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1258 X0
       have i₂ := eq509504 X0 (σ X0)
       grind)
    | exact superpose eq509504 eq1258
    | (have j1 := eq509504 X1 (σ X0)
       grind)
    | (have r₁ := eq1258 (M.op X1 X1)
       have r₂ := eq509504 (τ (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1)))) X1
       grind)
    | exact resolve eq1258 eq509504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258 eq509504
  have eq512776 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq512671 X0 X1
       grind)
    | (have r₁ := eq512671 X0 X1
       have r₂ := eq10 X0
       grind)
    | exact resolve eq512671 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512671
  have eq512996 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq512776 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq512776
    | (have j0 := eq512776 X0 X1
       grind)
    | exact resolve eq512776 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512776
  have eq513164 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq512996 X0 X1
       have i₂ := eq12073 X0
       grind)
    | exact superpose eq12073 eq512996
    | (have j0 := eq512996 X0 X1
       grind)
    | exact resolve eq512996 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512996
  have eq513287 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq513164 X0 X1
       have i₂ := eq12083 X0
       grind)
    | exact superpose eq12083 eq513164
    | (have j0 := eq513164 X0 X1
       grind)
    | exact resolve eq513164 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513164
  have eq527438 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X1 ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq513287 X1 (σ X0)
       grind)
    | exact superpose eq513287 eq15
    | (have j1 := eq513287 X1 (σ X0)
       grind)
    | exact resolve eq15 eq513287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513287
  have eq560044 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq527438 x y
       grind)
    | exact superpose eq527438 eq16
    | (have j1 := eq527438 x y
       grind)
    | exact resolve eq16 eq527438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527438
  have eq563434 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq560044
       have i₂ := eq508230 x y
       grind)
    | exact superpose eq508230 eq560044
    | (have j1 := eq508230 y y
       grind)
    | (have r₁ := eq560044
       have r₂ := eq508230 x y
       grind)
    | exact resolve eq560044 eq508230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508230 eq560044
  have eq563437 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq563434
  have eq563438 : y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq563437
  have eq563498 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12828 y
       have i₂ := eq563438
       grind)
    | exact superpose eq563438 eq12828
    | exact resolve eq12828 eq563438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563438
  have eq563644 : (σ y) = (σ (k y y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq563498
       have i₂ := eq12073 y
       grind)
    | exact superpose eq12073 eq563498
    | exact resolve eq563498 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563498
  have eq563661 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq563644
       have i₂ := eq12083 y
       grind)
    | exact superpose eq12083 eq563644
    | exact resolve eq563644 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563644
  have eq566885 : (σ x) = (σ y) ∨ (σ x) = (σ (k (k y y) y)) ∨ x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2688 y
       have i₂ := eq563661
       grind)
    | exact superpose eq563661 eq2688
    | (have j0 := eq2688 y
       grind)
    | exact resolve eq2688 eq563661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2688
  have eq566992 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq631 y y
       have i₂ := eq563661
       grind)
    | exact superpose eq563661 eq631
    | (have j0 := eq631 y y
       grind)
    | (have r₁ := eq631 y y
       have r₂ := eq563661
       grind)
    | exact resolve eq631 eq563661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631 eq563661
  have eq567061 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq566992
  have eq567069 : (σ y) = (σ (k y y)) ∨ (σ x) ≠ (σ y) ∨ x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq567061
       have i₂ := eq12073 y
       grind)
    | exact superpose eq12073 eq567061
    | exact resolve eq567061 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567061
  have eq567078 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq566885
       have i₂ := eq10381 y
       grind)
    | exact superpose eq10381 eq566885
    | exact resolve eq566885 eq10381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10381 eq566885
  have eq567091 : (σ y) = (σ (M.op y y)) ∨ (σ x) ≠ (σ y) ∨ x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq567069
       have i₂ := eq12083 y
       grind)
    | exact superpose eq12083 eq567069
    | exact resolve eq567069 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567069
  have eq567092 : (σ y) = (σ (M.op y y)) ∨ (σ x) ≠ (σ y) ∨ x = y ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq567091
  have eq567095 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq567078
       have i₂ := eq12083 y
       grind)
    | exact superpose eq12083 eq567078
    | exact resolve eq567078 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567078
  have eq567096 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq567095
  have eq567108 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq567096
       have r₂ := eq567092
       grind)
    | exact resolve eq567096 eq567092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567092 eq567096
  have eq567109 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq567108
       grind)
    | exact superpose eq567108 eq16
    | exact resolve eq16 eq567108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567108
  have eq567125 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq567109
       have i₂ := eq12073 x
       grind)
    | exact superpose eq12073 eq567109
    | exact resolve eq567109 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567109
  have eq567128 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq567125
       have i₂ := eq12083 x
       grind)
    | exact superpose eq12083 eq567125
    | exact resolve eq567125 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567125
  have eq567129 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq567128
  have eq567930 : (σ (σ y)) = (M.op (σ (σ y)) (σ (σ y))) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq13316 y
       have i₂ := eq567129
       grind)
    | exact superpose eq567129 eq13316
    | exact resolve eq13316 eq567129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13316 eq567129
  have eq568502 : (σ (σ y)) = (σ (k (σ y) (σ y))) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq567930
       have i₂ := eq12073 (σ y)
       grind)
    | exact superpose eq12073 eq567930
    | exact resolve eq567930 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567930
  have eq568602 : (σ (σ y)) = (σ (σ (k y y))) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq568502
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq568502
    | exact resolve eq568502 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568502
  have eq568654 : (σ x) = (σ (M.op y y)) ∨ (σ (σ y)) = (σ (σ (M.op y y))) := by
    first
    | (have i₁ := eq568602
       have i₂ := eq12083 y
       grind)
    | exact superpose eq12083 eq568602
    | exact resolve eq568602 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568602
  have eq575274 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (σ y)) = (σ (σ (M.op y y))) := by
    first
    | (have i₁ := eq12828 y
       have i₂ := eq568654
       grind)
    | exact superpose eq568654 eq12828
    | exact resolve eq12828 eq568654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575298 : (M.op y y) = (τ (σ x)) ∨ (σ (σ y)) = (σ (σ (M.op y y))) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq568654
       grind)
    | exact superpose eq568654 eq10
    | exact resolve eq10 eq568654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568654
  have eq575839 : x = (M.op y y) ∨ (σ (σ y)) = (σ (σ (M.op y y))) := by
    first
    | (have i₁ := eq575298
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq575298
    | exact resolve eq575298 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575298
  have eq576312 : x = (M.op x y) ∨ (σ (σ y)) = (σ (σ (M.op y y))) := by
    first
    | (have i₁ := eq922 y y
       have i₂ := eq575839
       grind)
    | exact superpose eq575839 eq922
    | exact resolve eq922 eq575839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922 eq575839
  have eq581192 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (σ y)) = (σ (σ (M.op y y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq575274
       grind)
    | exact superpose eq575274 eq16
    | exact resolve eq16 eq575274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575274
  have eq583225 : (σ x) ≠ (σ x) ∨ (σ (σ y)) = (σ (σ (M.op y y))) ∨ (σ (σ y)) = (σ (σ (M.op y y))) := by
    first
    | (have i₁ := eq581192
       have i₂ := eq576312
       grind)
    | exact superpose eq576312 eq581192
    | exact resolve eq581192 eq576312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576312 eq581192
  have eq583227 : (σ x) ≠ (σ x) ∨ (σ (σ y)) = (σ (σ (M.op y y))) := by grind
  clear eq583225
  have eq583228 : (σ (σ y)) = (σ (σ (M.op y y))) := by grind
  clear eq583227
  have eq583280 : (σ (M.op y y)) = (τ (σ (σ y))) := by
    first
    | (have i₁ := eq10 (σ (M.op y y))
       have i₂ := eq583228
       grind)
    | exact superpose eq583228 eq10
    | exact resolve eq10 eq583228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583228
  have eq583880 : (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq583280
       have i₂ := eq10 (σ y)
       grind)
    | exact superpose eq10 eq583280
    | exact resolve eq583280 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583280
  have eq585806 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq583880
       grind)
    | exact superpose eq583880 eq10
    | exact resolve eq10 eq583880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq586387 : y = (M.op y y) := by
    first
    | (have i₁ := eq585806
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq585806
    | exact resolve eq585806 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585806
  have eq587135 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq104 x y
       have i₂ := eq10574
       grind)
    | exact superpose eq10574 eq104
    | (have j0 := eq104 x y
       grind)
    | exact resolve eq104 eq10574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq10574
  have eq587220 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq587135
  have eq587235 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq587220
       have r₂ := eq583880
       grind)
    | exact resolve eq587220 eq583880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587220
  have eq587243 : (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq587235
       have i₂ := eq12073 y
       grind)
    | exact superpose eq12073 eq587235
    | exact resolve eq587235 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587235
  have eq587250 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq587243
       have i₂ := eq12083 y
       grind)
    | exact superpose eq12083 eq587243
    | exact resolve eq587243 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587243
  have eq587256 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq587250
       have i₂ := eq583880
       grind)
    | exact superpose eq583880 eq587250
    | exact resolve eq587250 eq583880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587250
  have eq587262 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq587256
       have i₂ := eq586387
       grind)
    | exact superpose eq586387 eq587256
    | exact resolve eq587256 eq586387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587256
  have eq642583 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq587262
       grind)
    | exact superpose eq587262 eq16
    | exact resolve eq16 eq587262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587262
  have eq642650 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq642583
       have i₂ := eq12073 x
       grind)
    | exact superpose eq12073 eq642583
    | exact resolve eq642583 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642583
  have eq642652 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq642650
       have i₂ := eq12083 x
       grind)
    | exact superpose eq12083 eq642650
    | exact resolve eq642650 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642650
  have eq642653 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq642652
  have eq642659 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq642653
       grind)
    | exact superpose eq642653 eq16
    | exact resolve eq16 eq642653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq642689 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq642653
       grind)
    | exact superpose eq642653 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq642653
       grind)
    | exact resolve eq12 eq642653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642653
  have eq642755 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq642689
  have eq642771 : (σ (k x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq642755
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq642755
    | exact resolve eq642755 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642755
  have eq642798 : (σ (k x y)) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq642771
       have i₂ := eq12073 y
       grind)
    | exact superpose eq12073 eq642771
    | exact resolve eq642771 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642771
  have eq642814 : (σ (k x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq642798
       have i₂ := eq12083 y
       grind)
    | exact superpose eq12083 eq642798
    | exact resolve eq642798 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642798
  have eq642820 : (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq642814
       have i₂ := eq583880
       grind)
    | exact superpose eq583880 eq642814
    | exact resolve eq642814 eq583880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642814
  have eq644993 : y = (τ (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq642820
       grind)
    | exact superpose eq642820 eq10
    | exact resolve eq10 eq642820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642820
  have eq645591 : x = y ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq644993
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq644993
    | exact resolve eq644993 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644993
  have eq647920 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq645591
       grind)
    | exact superpose eq645591 eq16
    | exact resolve eq16 eq645591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645591
  have eq647987 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq647920
       have i₂ := eq12073 x
       grind)
    | exact superpose eq12073 eq647920
    | exact resolve eq647920 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647920
  have eq647989 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq647987
       have i₂ := eq12083 x
       grind)
    | exact superpose eq12083 eq647987
    | exact resolve eq647987 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647987
  have eq647990 : (σ y) = (σ (k x y)) := by grind
  clear eq647989
  have eq648019 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq647990
       grind)
    | exact superpose eq647990 eq10
    | exact resolve eq10 eq647990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647990
  have eq648562 : y = (k x y) := by
    first
    | (have i₁ := eq648019
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq648019
    | exact resolve eq648019 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648019
  have eq650547 : y ≠ y ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq658 x y
       have i₂ := eq648562
       grind)
    | exact superpose eq648562 eq658
    | (have j0 := eq658 x y
       grind)
    | (have r₁ := eq658 x y
       have r₂ := eq648562
       grind)
    | exact resolve eq658 eq648562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq648562
  have eq650612 : x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq650547
  have eq650666 : x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq650612
       have i₂ := eq586387
       grind)
    | exact superpose eq586387 eq650612
    | exact resolve eq650612 eq586387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586387 eq650612
  have eq650697 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq650666
       grind)
    | exact superpose eq650666 eq16
    | exact resolve eq16 eq650666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650666
  have eq650768 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq650697
       have i₂ := eq12073 x
       grind)
    | exact superpose eq12073 eq650697
    | exact resolve eq650697 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650697
  have eq650770 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq650768
       have i₂ := eq12083 x
       grind)
    | exact superpose eq12083 eq650768
    | exact resolve eq650768 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650768
  have eq650771 : y = (M.op x y) := by grind
  clear eq650770
  have eq652462 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq642659
       have i₂ := eq650771
       grind)
    | exact superpose eq650771 eq642659
    | exact resolve eq642659 eq650771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642659
  have eq652551 : (σ x) = (σ y) := by grind
  clear eq652462
  have eq652572 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq652551
       grind)
    | exact superpose eq652551 eq16
    | exact resolve eq16 eq652551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652874 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ x)) := by
    first
    | (have i₁ := eq12828 y
       have i₂ := eq652551
       grind)
    | exact superpose eq652551 eq12828
    | exact resolve eq12828 eq652551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12828
  have eq652979 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq652874
       have i₂ := eq583880
       grind)
    | exact superpose eq583880 eq652874
    | exact resolve eq652874 eq583880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583880 eq652874
  have eq653181 : (σ (M.op x y)) ≠ (σ (k x x)) := by
    first
    | (have i₁ := eq652572
       have i₂ := eq12073 x
       grind)
    | exact superpose eq12073 eq652572
    | exact resolve eq652572 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652572
  have eq653218 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq652979
       have i₂ := eq652551
       grind)
    | exact superpose eq652551 eq652979
    | exact resolve eq652979 eq652551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652979
  have eq653341 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq653181
       have i₂ := eq12083 x
       grind)
    | exact superpose eq12083 eq653181
    | exact resolve eq653181 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653181
  have eq653355 : (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq653218
       have i₂ := eq12073 x
       grind)
    | exact superpose eq12073 eq653218
    | exact resolve eq653218 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12073 eq653218
  have eq653471 : (σ y) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq653341
       have i₂ := eq650771
       grind)
    | exact superpose eq650771 eq653341
    | exact resolve eq653341 eq650771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650771 eq653341
  have eq653479 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq653355
       have i₂ := eq12083 x
       grind)
    | exact superpose eq12083 eq653355
    | exact resolve eq653355 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12083 eq653355
  have eq653556 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq653471
       have i₂ := eq652551
       grind)
    | exact superpose eq652551 eq653471
    | exact resolve eq653471 eq652551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652551 eq653471
  have eq653619 : False := by grind
  exact eq653619

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_x_y_pyy_pxx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
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
  have eq25 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
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
  have eq29 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 X0) X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq21
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
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq84 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op (τ X0) X1) = X1 := by
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
  have eq87 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (τ X1) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq99 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq47
    | exact resolve eq47 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq21 (σ X0)
       have i₂ := eq47 X0
       grind)
    | exact superpose eq47 eq21
    | (have j1 := eq47 X0
       grind)
    | exact resolve eq21 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq106 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq47 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq111 : ∀ X0 X1 X2 X3 : G, (σ (k (k X0 (τ X1)) (k (τ X2) X3))) = (k (k (σ X0) X1) (k X2 (σ X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X2 X3 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq25
    | exact resolve eq25 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq153 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
  have eq156 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq226 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq106 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq106
    | (have j0 := eq106 (τ X0)
       grind)
    | exact resolve eq106 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq226 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq226
    | (have j0 := eq226 X0
       grind)
    | exact resolve eq226 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq230 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq227 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq227
    | (have j0 := eq227 X0
       grind)
    | exact resolve eq227 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq335 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq84 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq84
    | exact resolve eq84 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq366 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq335 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq335
    | (have j0 := eq335 X0 X1
       grind)
    | exact resolve eq335 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq461 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (M.op (σ (k (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq102 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq102
    | exact resolve eq102 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq476 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (k (σ (τ X0)) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq461 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq461
    | (have j0 := eq461 X0
       grind)
    | exact resolve eq461 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq480 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq476 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq476
    | (have j0 := eq476 X0
       grind)
    | exact resolve eq476 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq606 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq87 (k (τ x) (τ x)) x
       have i₂ := eq480 (τ x)
       grind)
    | exact superpose eq480 eq87
    | (have j0 := eq87 (k (τ X0) (τ X0)) X0
       have j1 := eq480 (τ X0)
       grind)
    | exact resolve eq87 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq480
  have eq632 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq606 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq641 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq632 X0
       have j1 := eq230 (τ X0)
       grind)
    | (have r₁ := eq632 X0
       have r₂ := eq230 (τ X0)
       grind)
    | exact resolve eq632 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230 eq632
  have eq645 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq641 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq641
    | (have j0 := eq641 X0
       grind)
    | exact resolve eq641 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq641
  have eq646 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq645 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq645
    | (have j0 := eq645 X0
       grind)
    | exact resolve eq645 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq768 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (τ X0) (τ X0)
       have i₂ := eq646 X0
       grind)
    | exact superpose eq646 eq12
    | (have j1 := eq646 X0
       grind)
    | (have r₁ := eq12 (τ X0) (τ X0)
       have r₂ := eq646 X0
       grind)
    | exact resolve eq12 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq769 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ X0)) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq768 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq771 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq769 X0
       have i₂ := eq38 X0 X0
       grind)
    | exact superpose eq38 eq769
    | (have j0 := eq769 X0
       grind)
    | exact resolve eq769 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
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
       have r₂ := eq366 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq153
       have r₂ := eq366 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq153 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq778 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq777
  have eq798 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq27 (k (σ X0) (σ X0)) X0
       have i₂ := eq771 (σ X0)
       grind)
    | exact superpose eq771 eq27
    | (have j1 := eq771 (σ X0)
       grind)
    | exact resolve eq27 eq771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq805 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq798 x
       have i₂ := eq27 (σ x) x
       grind)
    | exact superpose eq27 eq798
    | (have j0 := eq798 X0
       grind)
    | exact resolve eq798 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq822 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq805 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq805
    | (have j0 := eq805 X0
       grind)
    | exact resolve eq805 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805
  have eq837 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq822 X0
       have i₂ := eq27 (σ X0) X0
       grind)
    | exact superpose eq27 eq822
    | (have j0 := eq822 X0
       grind)
    | exact resolve eq822 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq851 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq837 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq837
    | (have j0 := eq837 X0
       grind)
    | exact resolve eq837 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq872 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq851
  have eq898 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq872 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq915 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq898 X0
       have j1 := eq29 X0
       grind)
    | (have r₁ := eq898 X0
       have r₂ := eq29 X0
       grind)
    | exact resolve eq898 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq898
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
  have eq2086 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) ∨ (M.op (k X0 X1) (k X0 X1)) = (σ (k (k (τ X0) (τ X1)) (k (τ X0) (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq99 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq99
    | exact resolve eq99 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq2146 : ∀ X0 X1 : G, (M.op (k X0 X1) (k X0 X1)) = (k (k (σ (τ X0)) X1) (k X0 (σ (τ X1)))) ∨ (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2086 X0 X1
       have i₂ := eq111 (τ X0) X1 X0 (τ X1)
       grind)
    | exact superpose eq111 eq2086
    | (have j0 := eq2086 X0 X1
       grind)
    | exact resolve eq2086 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq2086
  have eq2155 : ∀ X0 X1 : G, (M.op (k X0 X1) (k X0 X1)) = (k (k (σ (τ X0)) X1) (k X0 X1)) ∨ (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2146 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2146
    | (have j0 := eq2146 X0 X1
       grind)
    | exact resolve eq2146 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2146
  have eq2160 : ∀ X0 X1 : G, (k (k X0 X1) (k X0 X1)) = (M.op (k X0 X1) (k X0 X1)) ∨ (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2155 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2155
    | (have j0 := eq2155 X0 X1
       grind)
    | exact resolve eq2155 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2155
  have eq2164 : ∀ X0 X1 : G, (k (k X0 X1) (k X0 X1)) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2160 X0 X1
       have j1 := eq12 (k X0 X1) (k X0 X1)
       grind)
    | (have r₁ := eq2160 X0 X1
       have r₂ := eq12 (k X0 X1) (k X0 X1)
       grind)
    | exact resolve eq2160 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2160
  have eq2214 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2164 (M.op X0 X0) X0
       have i₂ := eq915 X0
       grind)
    | exact superpose eq915 eq2164
    | exact resolve eq2164 eq915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915 eq2164
  have eq2477 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2214 (τ X0)
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq2214
    | (have j1 := eq77 X0
       grind)
    | exact resolve eq2214 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq2214
  have eq2491 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2477 X0
       have i₂ := eq38 X0 X0
       grind)
    | exact superpose eq38 eq2477
    | (have j0 := eq2477 X0
       grind)
    | exact resolve eq2477 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq2477
  have eq2492 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq2491 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2491
  have eq2577 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2492 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2492
    | exact resolve eq2492 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2492
  have eq2629 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq2577 X0
       have i₂ := eq27 (σ X0) X0
       grind)
    | exact superpose eq27 eq2577
    | exact resolve eq2577 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2577
  have eq2636 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2629 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2629
    | exact resolve eq2629 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2629
  have eq2643 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq106 X0
       have i₂ := eq2636 X0
       grind)
    | exact superpose eq2636 eq106
    | (have j0 := eq106 X0
       grind)
    | exact resolve eq106 eq2636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq2667 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq2636 (σ X0)
       grind)
    | exact superpose eq2636 eq15
    | exact resolve eq15 eq2636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2691 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2667 X0
       have i₂ := eq2636 X0
       grind)
    | exact superpose eq2636 eq2667
    | exact resolve eq2667 eq2636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2636 eq2667
  have eq2928 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1062 (σ X0) (σ X0)
       have i₂ := eq2691 X0
       grind)
    | exact superpose eq2691 eq1062
    | exact resolve eq1062 eq2691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62090 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
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
  have eq62091 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq62090
       have r₂ := eq2691 x
       grind)
    | exact resolve eq62090 eq2691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62090
  have eq62696 : y ≠ y ∨ (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq62091
       grind)
    | exact superpose eq62091 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq62091
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq62091
       grind)
    | exact resolve eq12 eq62091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62703 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1062 y x
       have i₂ := eq62091
       grind)
    | exact superpose eq62091 eq1062
    | exact resolve eq1062 eq62091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62091
  have eq62719 : (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq62696
  have eq62735 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1062 (σ y) (σ x)
       have i₂ := eq62703
       grind)
    | exact superpose eq62703 eq1062
    | exact resolve eq1062 eq62703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062 eq62703
  have eq62753 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq62735
       have i₂ := eq2691 y
       grind)
    | exact superpose eq2691 eq62735
    | exact resolve eq62735 eq2691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62735
  have eq63147 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq62753
       grind)
    | exact superpose eq62753 eq10
    | exact resolve eq10 eq62753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62753
  have eq63274 : x = y ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq63147
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq63147
    | exact resolve eq63147 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63147
  have eq63562 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq63274
       grind)
    | exact superpose eq63274 eq16
    | exact resolve eq16 eq63274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63274
  have eq63563 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq63562
       have r₂ := eq2691 x
       grind)
    | exact resolve eq63562 eq2691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63562
  have eq63583 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2928 y
       have i₂ := eq63563
       grind)
    | exact superpose eq63563 eq2928
    | exact resolve eq2928 eq63563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2928 eq63563
  have eq63645 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq2643 y
       grind)
    | (have r₁ := eq63583
       have r₂ := eq2643 y
       grind)
    | exact resolve eq63583 eq2643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2643 eq63583
  have eq63655 : (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq63645
       have i₂ := eq2691 y
       grind)
    | exact superpose eq2691 eq63645
    | exact resolve eq63645 eq2691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63645
  have eq168477 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq156 x y
       have i₂ := eq62719
       grind)
    | exact superpose eq62719 eq156
    | (have j0 := eq156 x y
       grind)
    | exact resolve eq156 eq62719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156 eq62719
  have eq168495 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq168477
  have eq168505 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq168495
       have r₂ := eq63655
       grind)
    | exact resolve eq168495 eq63655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168495
  have eq168509 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq168505
       grind)
    | exact superpose eq168505 eq16
    | exact resolve eq16 eq168505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168546 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq168505
       grind)
    | exact superpose eq168505 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq168505
       grind)
    | exact resolve eq12 eq168505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168505
  have eq168574 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq168546
  have eq168582 : (σ (k x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq168574
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq168574
    | exact resolve eq168574 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168574
  have eq168599 : (σ (k x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq168582
       have i₂ := eq2691 y
       grind)
    | exact superpose eq2691 eq168582
    | exact resolve eq168582 eq2691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168582
  have eq168605 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq168599
       have i₂ := eq63655
       grind)
    | exact superpose eq63655 eq168599
    | exact resolve eq168599 eq63655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63655 eq168599
  have eq169461 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq366 x y
       have i₂ := eq168605
       grind)
    | exact superpose eq168605 eq366
    | (have j0 := eq366 x y
       grind)
    | exact resolve eq366 eq168605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366 eq168605
  have eq169721 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq169461
       have r₂ := eq168509
       grind)
    | exact resolve eq169461 eq168509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169461
  have eq171289 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq168509
       have i₂ := eq169721
       grind)
    | exact superpose eq169721 eq168509
    | exact resolve eq168509 eq169721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168509 eq169721
  have eq171397 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq171289
  have eq171398 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq171397
  have eq171445 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq171398
       grind)
    | exact superpose eq171398 eq10
    | exact resolve eq10 eq171398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171398
  have eq171711 : x = y ∨ x = y := by
    first
    | (have i₁ := eq171445
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq171445
    | exact resolve eq171445 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171445
  have eq171712 : x = y := by grind
  clear eq171711
  have eq172719 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq171712
       grind)
    | exact superpose eq171712 eq16
    | exact resolve eq16 eq171712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171712
  have eq172913 : False := by grind
  exact eq172913

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,Y) else if X = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_x_y_pyy_pyy_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ X0 ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
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
  have eq25 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
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
  have eq29 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 X0) X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq21
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
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq84 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op (τ X0) X1) = X1 := by
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
  have eq87 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (τ X1) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq99 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq47
    | exact resolve eq47 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq21 (σ X0)
       have i₂ := eq47 X0
       grind)
    | exact superpose eq47 eq21
    | (have j1 := eq47 X0
       grind)
    | exact resolve eq21 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq106 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq47 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq111 : ∀ X0 X1 X2 X3 : G, (σ (k (k X0 (τ X1)) (k (τ X2) X3))) = (k (k (σ X0) X1) (k X2 (σ X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X2 X3 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq25
    | exact resolve eq25 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq153 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
  have eq156 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq226 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq106 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq106
    | (have j0 := eq106 (τ X0)
       grind)
    | exact resolve eq106 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq226 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq226
    | (have j0 := eq226 X0
       grind)
    | exact resolve eq226 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq230 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq227 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq227
    | (have j0 := eq227 X0
       grind)
    | exact resolve eq227 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq335 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq84 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq84
    | exact resolve eq84 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq366 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq335 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq335
    | (have j0 := eq335 X0 X1
       grind)
    | exact resolve eq335 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq461 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (M.op (σ (k (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq102 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq102
    | exact resolve eq102 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq476 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (k (σ (τ X0)) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq461 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq461
    | (have j0 := eq461 X0
       grind)
    | exact resolve eq461 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq480 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq476 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq476
    | (have j0 := eq476 X0
       grind)
    | exact resolve eq476 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq606 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq87 (k (τ x) (τ x)) x
       have i₂ := eq480 (τ x)
       grind)
    | exact superpose eq480 eq87
    | (have j0 := eq87 (k (τ X0) (τ X0)) X0
       have j1 := eq480 (τ X0)
       grind)
    | exact resolve eq87 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq480
  have eq632 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq606 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq641 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq632 X0
       have j1 := eq230 (τ X0)
       grind)
    | (have r₁ := eq632 X0
       have r₂ := eq230 (τ X0)
       grind)
    | exact resolve eq632 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230 eq632
  have eq645 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq641 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq641
    | (have j0 := eq641 X0
       grind)
    | exact resolve eq641 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq641
  have eq646 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq645 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq645
    | (have j0 := eq645 X0
       grind)
    | exact resolve eq645 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq768 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (τ X0) (τ X0)
       have i₂ := eq646 X0
       grind)
    | exact superpose eq646 eq12
    | (have j1 := eq646 X0
       grind)
    | (have r₁ := eq12 (τ X0) (τ X0)
       have r₂ := eq646 X0
       grind)
    | exact resolve eq12 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq769 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ X0)) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq768 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq771 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq769 X0
       have i₂ := eq38 X0 X0
       grind)
    | exact superpose eq38 eq769
    | (have j0 := eq769 X0
       grind)
    | exact resolve eq769 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
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
       have r₂ := eq366 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq153
       have r₂ := eq366 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq153 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq778 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq777
  have eq798 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq27 (k (σ X0) (σ X0)) X0
       have i₂ := eq771 (σ X0)
       grind)
    | exact superpose eq771 eq27
    | (have j1 := eq771 (σ X0)
       grind)
    | exact resolve eq27 eq771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq805 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq798 x
       have i₂ := eq27 (σ x) x
       grind)
    | exact superpose eq27 eq798
    | (have j0 := eq798 X0
       grind)
    | exact resolve eq798 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq822 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq805 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq805
    | (have j0 := eq805 X0
       grind)
    | exact resolve eq805 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805
  have eq837 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq822 X0
       have i₂ := eq27 (σ X0) X0
       grind)
    | exact superpose eq27 eq822
    | (have j0 := eq822 X0
       grind)
    | exact resolve eq822 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq851 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq837 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq837
    | (have j0 := eq837 X0
       grind)
    | exact resolve eq837 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq872 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq851
  have eq898 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq872 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq915 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq898 X0
       have j1 := eq29 X0
       grind)
    | (have r₁ := eq898 X0
       have r₂ := eq29 X0
       grind)
    | exact resolve eq898 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq898
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
  have eq2086 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) ∨ (M.op (k X0 X1) (k X0 X1)) = (σ (k (k (τ X0) (τ X1)) (k (τ X0) (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq99 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq99
    | exact resolve eq99 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq2146 : ∀ X0 X1 : G, (M.op (k X0 X1) (k X0 X1)) = (k (k (σ (τ X0)) X1) (k X0 (σ (τ X1)))) ∨ (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2086 X0 X1
       have i₂ := eq111 (τ X0) X1 X0 (τ X1)
       grind)
    | exact superpose eq111 eq2086
    | (have j0 := eq2086 X0 X1
       grind)
    | exact resolve eq2086 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq2086
  have eq2155 : ∀ X0 X1 : G, (M.op (k X0 X1) (k X0 X1)) = (k (k (σ (τ X0)) X1) (k X0 X1)) ∨ (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2146 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2146
    | (have j0 := eq2146 X0 X1
       grind)
    | exact resolve eq2146 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2146
  have eq2160 : ∀ X0 X1 : G, (k (k X0 X1) (k X0 X1)) = (M.op (k X0 X1) (k X0 X1)) ∨ (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2155 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2155
    | (have j0 := eq2155 X0 X1
       grind)
    | exact resolve eq2155 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2155
  have eq2164 : ∀ X0 X1 : G, (k (k X0 X1) (k X0 X1)) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2160 X0 X1
       have j1 := eq12 (k X0 X1) (k X0 X1)
       grind)
    | (have r₁ := eq2160 X0 X1
       have r₂ := eq12 (k X0 X1) (k X0 X1)
       grind)
    | exact resolve eq2160 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2160
  have eq2214 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2164 (M.op X0 X0) X0
       have i₂ := eq915 X0
       grind)
    | exact superpose eq915 eq2164
    | exact resolve eq2164 eq915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915 eq2164
  have eq2477 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2214 (τ X0)
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq2214
    | (have j1 := eq77 X0
       grind)
    | exact resolve eq2214 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq2214
  have eq2491 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2477 X0
       have i₂ := eq38 X0 X0
       grind)
    | exact superpose eq38 eq2477
    | (have j0 := eq2477 X0
       grind)
    | exact resolve eq2477 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq2477
  have eq2492 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq2491 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2491
  have eq2577 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2492 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2492
    | exact resolve eq2492 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2492
  have eq2629 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq2577 X0
       have i₂ := eq27 (σ X0) X0
       grind)
    | exact superpose eq27 eq2577
    | exact resolve eq2577 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2577
  have eq2636 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2629 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2629
    | exact resolve eq2629 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2629
  have eq2643 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq106 X0
       have i₂ := eq2636 X0
       grind)
    | exact superpose eq2636 eq106
    | (have j0 := eq106 X0
       grind)
    | exact resolve eq106 eq2636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq2667 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq2636 (σ X0)
       grind)
    | exact superpose eq2636 eq15
    | exact resolve eq15 eq2636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2691 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2667 X0
       have i₂ := eq2636 X0
       grind)
    | exact superpose eq2636 eq2667
    | exact resolve eq2667 eq2636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2636 eq2667
  have eq2928 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1062 (σ X0) (σ X0)
       have i₂ := eq2691 X0
       grind)
    | exact superpose eq2691 eq1062
    | exact resolve eq1062 eq2691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62090 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
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
  have eq62091 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq62090
       have r₂ := eq2691 x
       grind)
    | exact resolve eq62090 eq2691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62090
  have eq62696 : y ≠ y ∨ (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq62091
       grind)
    | exact superpose eq62091 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq62091
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq62091
       grind)
    | exact resolve eq12 eq62091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62703 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1062 y x
       have i₂ := eq62091
       grind)
    | exact superpose eq62091 eq1062
    | exact resolve eq1062 eq62091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62091
  have eq62719 : (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq62696
  have eq62735 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1062 (σ y) (σ x)
       have i₂ := eq62703
       grind)
    | exact superpose eq62703 eq1062
    | exact resolve eq1062 eq62703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062 eq62703
  have eq62753 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq62735
       have i₂ := eq2691 y
       grind)
    | exact superpose eq2691 eq62735
    | exact resolve eq62735 eq2691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62735
  have eq63147 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq62753
       grind)
    | exact superpose eq62753 eq10
    | exact resolve eq10 eq62753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62753
  have eq63274 : x = y ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq63147
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq63147
    | exact resolve eq63147 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63147
  have eq63562 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq63274
       grind)
    | exact superpose eq63274 eq16
    | exact resolve eq16 eq63274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63274
  have eq63563 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq63562
       have r₂ := eq2691 x
       grind)
    | exact resolve eq63562 eq2691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63562
  have eq63583 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2928 y
       have i₂ := eq63563
       grind)
    | exact superpose eq63563 eq2928
    | exact resolve eq2928 eq63563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2928 eq63563
  have eq63645 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq2643 y
       grind)
    | (have r₁ := eq63583
       have r₂ := eq2643 y
       grind)
    | exact resolve eq63583 eq2643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2643 eq63583
  have eq63655 : (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq63645
       have i₂ := eq2691 y
       grind)
    | exact superpose eq2691 eq63645
    | exact resolve eq63645 eq2691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63645
  have eq168477 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq156 x y
       have i₂ := eq62719
       grind)
    | exact superpose eq62719 eq156
    | (have j0 := eq156 x y
       grind)
    | exact resolve eq156 eq62719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156 eq62719
  have eq168495 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq168477
  have eq168505 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq168495
       have r₂ := eq63655
       grind)
    | exact resolve eq168495 eq63655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168495
  have eq168509 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq168505
       grind)
    | exact superpose eq168505 eq16
    | exact resolve eq16 eq168505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168546 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq168505
       grind)
    | exact superpose eq168505 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq168505
       grind)
    | exact resolve eq12 eq168505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168505
  have eq168574 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq168546
  have eq168582 : (σ (k x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq168574
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq168574
    | exact resolve eq168574 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168574
  have eq168599 : (σ (k x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq168582
       have i₂ := eq2691 y
       grind)
    | exact superpose eq2691 eq168582
    | exact resolve eq168582 eq2691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168582
  have eq168605 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq168599
       have i₂ := eq63655
       grind)
    | exact superpose eq63655 eq168599
    | exact resolve eq168599 eq63655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63655 eq168599
  have eq169461 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq366 x y
       have i₂ := eq168605
       grind)
    | exact superpose eq168605 eq366
    | (have j0 := eq366 x y
       grind)
    | exact resolve eq366 eq168605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366 eq168605
  have eq169721 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq169461
       have r₂ := eq168509
       grind)
    | exact resolve eq169461 eq168509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169461
  have eq171289 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq168509
       have i₂ := eq169721
       grind)
    | exact superpose eq169721 eq168509
    | exact resolve eq168509 eq169721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168509 eq169721
  have eq171397 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq171289
  have eq171398 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq171397
  have eq171445 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq171398
       grind)
    | exact superpose eq171398 eq10
    | exact resolve eq10 eq171398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171398
  have eq171711 : x = y ∨ x = y := by
    first
    | (have i₁ := eq171445
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq171445
    | exact resolve eq171445 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171445
  have eq171712 : x = y := by grind
  clear eq171711
  have eq172719 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq171712
       grind)
    | exact superpose eq171712 eq16
    | exact resolve eq16 eq171712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171712
  have eq172913 : False := by grind
  exact eq172913
