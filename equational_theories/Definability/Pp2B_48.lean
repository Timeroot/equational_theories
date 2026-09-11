import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq21 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq21
    | exact resolve eq21 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq41 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq44 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 ∨ (M.op (M.op (M.op X1 X2) X0) X1) = (M.op (M.op (M.op (M.op X1 X2) X0) X1) (M.op (M.op (M.op X1 X2) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op (M.op X1 X2) X0) X1)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X0 (M.op (M.op (M.op X1 X2) X0) X1)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op (M.op X1 X2) X0) X1)
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (M.op (M.op (M.op (M.op X1 X2) X0) X1) (M.op (M.op (M.op X1 X2) X0) X1)) ∨ (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq44 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq60 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41 (k X0 (τ X1)) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq41
    | exact resolve eq41 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq74 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
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
  have eq100 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq25 X1 X2 X0
       grind)
    | exact superpose eq25 eq21
    | exact resolve eq21 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 (k X1 (τ X0)) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq71
    | exact resolve eq71 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ X1) (σ X0)
       have i₂ := eq71 X1 X0
       grind)
    | exact superpose eq71 eq21
    | (have j1 := eq71 X1 X1
       grind)
    | exact resolve eq21 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq256 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X0) ≠ (M.op (M.op (M.op X0 X1) X2) X0) ∨ (M.op (M.op (M.op (M.op X0 X1) X2) X0) X3) = (k X3 (M.op (M.op (M.op X0 X1) X2) X0)) ∨ (k X2 (M.op (M.op (M.op X0 X1) X2) X0)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 (M.op (M.op (M.op X0 X1) X2) X0)
       have i₂ := eq49 X2 X0 X1
       grind)
    | exact superpose eq49 eq12
    | (have j0 := eq12 X3 (M.op (M.op (M.op X0 X1) X2) X0)
       have j1 := eq49 X2 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op (M.op X1 X2) X0) X1)
       have r₂ := eq49 X0 X1 X2
       grind)
    | exact resolve eq12 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq257 : ∀ X0 X1 X2 X3 : G, (k X2 (M.op (M.op (M.op X0 X1) X2) X0)) = X2 ∨ (M.op (M.op (M.op (M.op X0 X1) X2) X0) X3) = (k X3 (M.op (M.op (M.op X0 X1) X2) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq256 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq1310 : ∀ X0 X1 X2 : G, (τ (k (k (σ X0) X1) X2)) = (k (M.op (τ X1) X0) (τ X2)) ∨ (M.op (τ X1) X0) = X0 ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41 (M.op (τ X1) X0) X2
       have i₂ := eq74 X1 X0
       grind)
    | exact superpose eq74 eq41
    | (have j1 := eq74 X1 X0
       grind)
    | exact resolve eq41 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1319 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (k (M.op (τ X1) X0) (τ X2)) ∨ (M.op (τ X1) X0) = X0 ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1310 X0 X1 X2
       have i₂ := eq60 X0 X1 X2
       grind)
    | exact superpose eq60 eq1310
    | (have j0 := eq1310 X0 X1 X2
       grind)
    | exact resolve eq1310 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq1310
  have eq1836 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq169 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq1837 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1836 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836
  have eq2409 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) ≠ X0 ∨ (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq257 X1 X2 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq2414 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2409 X0 X1 X2
       grind)
    | (have r₁ := eq2409 X0 X1 X2
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq2409 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2409
  have eq2426 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2414 X0 X1 X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq2414
    | exact resolve eq2414 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2414
  have eq2465 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2426 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq2426
    | exact resolve eq2426 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2468 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2426 (M.op X0 X1) X0 X0
       have i₂ := eq25 X0 X1 X0
       grind)
    | exact superpose eq25 eq2426
    | exact resolve eq2426 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2426
  have eq2527 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 (M.op (σ X0) X1)
       have i₂ := eq2465 (σ X0) X1
       grind)
    | exact superpose eq2465 eq41
    | exact resolve eq41 eq2465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2528 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op (τ X0) X1)
       have i₂ := eq2465 (τ X0) X1
       grind)
    | exact superpose eq2465 eq17
    | exact resolve eq17 eq2465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2537 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2528 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2528
    | exact resolve eq2528 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2528
  have eq2538 : ∀ X0 X1 : G, (k X0 (τ (M.op (σ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2527 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2527
    | exact resolve eq2527 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2527
  have eq2660 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = (k (σ (M.op (τ X0) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) X1)
       have i₂ := eq2468 (τ X0) X1
       grind)
    | exact superpose eq2468 eq18
    | exact resolve eq18 eq2468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2706 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (τ (τ X0)) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (M.op (τ (τ X0)) X1))
       have i₂ := eq2537 (τ X0) X1
       grind)
    | exact superpose eq2537 eq17
    | exact resolve eq17 eq2537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2537
  have eq2719 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op (τ (τ X0)) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2706 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2706
    | exact resolve eq2706 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2706
  have eq2875 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op (σ (σ X0)) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 (τ (M.op (σ (σ X0)) X1))
       have i₂ := eq2538 (σ X0) X1
       grind)
    | exact superpose eq2538 eq41
    | exact resolve eq41 eq2538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq2888 : ∀ X0 X1 : G, (k X0 (τ (τ (M.op (σ (σ X0)) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2875 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2875
    | exact resolve eq2875 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2875
  have eq3645 : ∀ X0 X1 X2 : G, (k X2 (σ (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ (τ X2))) ∨ (σ (τ X2)) = (M.op (k (σ X0) X1) (σ (τ X2))) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X2 (k X0 (τ X1))
       have i₂ := eq160 X0 X1 (τ X2)
       grind)
    | exact superpose eq160 eq17
    | (have j1 := eq160 X0 X1 (τ X2)
       grind)
    | exact resolve eq17 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq3686 : ∀ X0 X1 X2 : G, (k X2 (σ (k X0 (τ X1)))) = (M.op (k (σ X0) X1) X2) ∨ (σ (τ X2)) = (M.op (k (σ X0) X1) (σ (τ X2))) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3645 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq3645
    | (have j0 := eq3645 X0 X1 X2
       grind)
    | exact resolve eq3645 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3645
  have eq3704 : ∀ X0 X1 X2 : G, (k X2 (k (σ X0) X1)) = (M.op (k (σ X0) X1) X2) ∨ (σ (τ X2)) = (M.op (k (σ X0) X1) (σ (τ X2))) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3686 X0 X1 X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq3686
    | (have j0 := eq3686 X0 X1 X2
       grind)
    | exact resolve eq3686 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3686
  have eq3721 : ∀ X0 X1 X2 : G, (k X2 (k (σ X0) X1)) = (M.op (k (σ X0) X1) X2) ∨ (σ (τ X2)) = (M.op (k (σ X0) X1) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3704 X0 X1 X2
       have j1 := eq12 X2 (k (σ X0) X1)
       grind)
    | (have r₁ := eq3704 X0 X1 X2
       have r₂ := eq12 X0 (k (σ X0) X1)
       grind)
    | exact resolve eq3704 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3704
  have eq3738 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) X2) = X2 ∨ (k X2 (k (σ X0) X1)) = (M.op (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3721 X0 X1 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3721
    | (have j0 := eq3721 X0 X1 X2
       grind)
    | exact resolve eq3721 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3721
  have eq5667 : ∀ X0 : G, (M.op (σ (k (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1837 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1837
    | exact resolve eq1837 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1837
  have eq5796 : ∀ X0 : G, (M.op (k (σ (τ X0)) X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5667 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq5667
    | (have j0 := eq5667 X0
       grind)
    | exact resolve eq5667 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5667
  have eq5804 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5796 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5796
    | (have j0 := eq5796 X0
       grind)
    | exact resolve eq5796 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5796
  have eq5812 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op X0 X1) (k X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (k X0 X0) X0
       have i₂ := eq5804 X0
       grind)
    | exact superpose eq5804 eq9
    | (have j1 := eq5804 X0
       grind)
    | exact resolve eq9 eq5804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5804
  have eq7984 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op X1 (M.op (M.op X0 X1) X0)) ∨ (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq100 X0 X0 X0
       have i₂ := eq5812 X0 X1
       grind)
    | exact superpose eq5812 eq100
    | (have j1 := eq5812 X0 X2
       grind)
    | exact resolve eq100 eq5812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq5812
  have eq8146 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7984 X0 X1 X2
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq7984
    | (have j0 := eq7984 X0 X1 X2
       grind)
    | exact resolve eq7984 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7984
  have eq16789 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq8146 X0 (M.op (M.op X0 X0) (k X0 X0)) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8146
  have eq16790 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq16789 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16789
  have eq16820 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 (k X0 X0) X0 X0
       have i₂ := eq16790 X0
       grind)
    | exact superpose eq16790 eq22
    | exact resolve eq22 eq16790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq16790
  have eq17115 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2468 (k X0 X0) X0
       have i₂ := eq16820 X0
       grind)
    | exact superpose eq16820 eq2468
    | exact resolve eq2468 eq16820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16820
  have eq19484 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3738 X0 (k (σ X0) (σ X0)) x
       have i₂ := eq17115 (σ X0)
       grind)
    | exact superpose eq17115 eq3738
    | exact resolve eq3738 eq17115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3738 eq17115
  have eq33931 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19484 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19484
    | exact resolve eq19484 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34003 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 X0
       have i₂ := eq19484 X0 X1
       grind)
    | exact superpose eq19484 eq35
    | (have j1 := eq19484 X0 X1
       grind)
    | exact resolve eq35 eq19484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34018 : ∀ X0 X1 : G, (M.op (σ (σ (M.op (τ (τ X0)) X1))) X0) = X0 ∨ (M.op (σ (σ (M.op (τ (τ X0)) X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2719 X0 X1
       have i₂ := eq19484 (σ (M.op (τ (τ X0)) X1)) X0
       grind)
    | exact superpose eq19484 eq2719
    | (have j1 := eq19484 (σ (M.op (τ (τ X0)) X1)) X0
       grind)
    | exact resolve eq2719 eq19484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34149 : ∀ X0 X1 : G, (σ (M.op (τ (σ X0)) X1)) = (M.op (σ X0) (σ (M.op (τ (σ X0)) X1))) ∨ (σ (M.op (τ (σ X0)) X1)) = (M.op (σ X0) (σ (M.op (τ (σ X0)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2660 (σ X0) X1
       have i₂ := eq19484 X0 (σ (M.op (τ (σ X0)) X1))
       grind)
    | exact superpose eq19484 eq2660
    | (have j1 := eq19484 X0 (σ (M.op (τ (σ X0)) X1))
       grind)
    | exact resolve eq2660 eq19484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2660 eq19484
  have eq34184 : ∀ X0 X1 : G, (σ (M.op (τ (σ X0)) X1)) = (M.op (σ X0) (σ (M.op (τ (σ X0)) X1))) := by
    intro X0 X1
    first
    | (have j0 := eq34149 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34149
  have eq34216 : ∀ X0 X1 : G, (M.op (σ (σ (M.op (τ (τ X0)) X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq34018 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34018
  have eq34268 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34184 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq34184
    | exact resolve eq34184 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34184
  have eq36295 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq33931 (τ X0) X1
       grind)
    | exact superpose eq33931 eq18
    | (have j1 := eq33931 (τ X0) X1
       grind)
    | exact resolve eq18 eq33931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36317 : ∀ X0 X1 : G, (M.op (τ (τ (M.op (σ (σ X0)) X1))) X0) = X0 ∨ (M.op (τ (τ (M.op (σ (σ X0)) X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2888 X0 X1
       have i₂ := eq33931 (τ (τ (M.op (σ (σ X0)) X1))) X0
       grind)
    | exact superpose eq33931 eq2888
    | (have j1 := eq33931 (τ (τ (M.op (σ (σ X0)) X1))) X0
       grind)
    | exact resolve eq2888 eq33931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2888
  have eq36455 : ∀ X0 X1 : G, (M.op (τ (τ (M.op (σ (σ X0)) X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq36317 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36317
  have eq144051 : ∀ X0 X1 : G, (k X1 (k (τ X0) X1)) = X1 ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2538 X1 X0
       have i₂ := eq34003 X1 X0
       grind)
    | exact superpose eq34003 eq2538
    | (have j1 := eq34003 X1 X0
       grind)
    | exact resolve eq2538 eq34003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2538 eq34003
  have eq144578 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (k (τ X1) (τ X0)))) ∨ (M.op (σ (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (k (τ X1) (τ X0))
       have i₂ := eq144051 X1 (τ X0)
       grind)
    | exact superpose eq144051 eq17
    | (have j1 := eq144051 X1 (τ X0)
       grind)
    | exact resolve eq17 eq144051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144051
  have eq144632 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (k (σ (τ X1)) X0)) ∨ (M.op (σ (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq144578 X0 X1
       have i₂ := eq18 X0 (τ X1)
       grind)
    | exact superpose eq18 eq144578
    | (have j0 := eq144578 X0 X1
       grind)
    | exact resolve eq144578 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144578
  have eq144683 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (k X1 X0)) ∨ (M.op (σ (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq144632 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq144632
    | (have j0 := eq144632 X0 X1
       grind)
    | exact resolve eq144632 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144632
  have eq144717 : ∀ X0 X1 : G, (k X0 (k X1 X0)) = X0 ∨ (M.op (σ (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq144683 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq144683
    | (have j0 := eq144683 X0 X1
       grind)
    | exact resolve eq144683 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144683
  have eq144742 : ∀ X0 X1 : G, (k X0 (k X1 X0)) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq144717 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq144717
    | (have j0 := eq144717 X0 X1
       grind)
    | exact resolve eq144717 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144717
  have eq145543 : ∀ X0 X1 : G, (M.op (k X1 X0) X0) = X0 ∨ (M.op (k X1 X0) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33931 (k X1 X0) X0
       have i₂ := eq144742 X0 X1
       grind)
    | exact superpose eq144742 eq33931
    | (have j0 := eq33931 (k X1 X0) X0
       have j1 := eq144742 (k X1 X0) X0
       grind)
    | exact resolve eq33931 eq144742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33931 eq144742
  have eq145589 : ∀ X0 X1 : G, (M.op (k X1 X0) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq145543 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145543
  have eq145905 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 (k X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 (k X1 X0) X0
       have i₂ := eq145589 X0 X1
       grind)
    | exact superpose eq145589 eq21
    | (have j1 := eq145589 X0 (k X1 X0)
       grind)
    | exact resolve eq21 eq145589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq145589
  have eq150027 : ∀ X0 X1 : G, (M.op (σ (σ (k X0 (τ (τ X1))))) X1) = X1 ∨ (M.op (τ (τ X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34216 X1 (k X0 (τ (τ X1)))
       have i₂ := eq145905 (τ (τ X1)) X0
       grind)
    | exact superpose eq145905 eq34216
    | (have j1 := eq145905 (σ (σ (k X0 (τ (τ X1))))) X1
       grind)
    | exact resolve eq34216 eq145905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34216
  have eq150251 : ∀ X0 X1 : G, (M.op (σ (k (σ X0) (τ X1))) X1) = X1 ∨ (M.op (τ (τ X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq150027 X0 X1
       have i₂ := eq18 (τ X1) X0
       grind)
    | exact superpose eq18 eq150027
    | (have j0 := eq150027 X0 X1
       grind)
    | exact resolve eq150027 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150027
  have eq150321 : ∀ X0 X1 : G, (M.op (τ (τ X1)) X0) = X0 ∨ (M.op (k (σ (σ X0)) X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq150251 X0 X1
       have i₂ := eq18 X1 (σ X0)
       grind)
    | exact superpose eq18 eq150251
    | (have j0 := eq150251 X0 X1
       grind)
    | exact resolve eq150251 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150251
  have eq159885 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq36295 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq36295
    | exact resolve eq36295 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36295
  have eq160251 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq159885 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq159885
    | (have j0 := eq159885 X0 X1
       grind)
    | exact resolve eq159885 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159885
  have eq221051 : ∀ X0 X1 : G, (k X1 (σ (σ X0))) = X1 ∨ (M.op (k (σ (σ X0)) X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2719 X1 X0
       have i₂ := eq150321 X0 X1
       grind)
    | exact superpose eq150321 eq2719
    | (have j1 := eq150321 X0 X1
       grind)
    | exact resolve eq2719 eq150321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2719 eq150321
  have eq225012 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (M.op (k (σ X0) X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq221051 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq221051
    | exact resolve eq221051 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221051
  have eq226555 : ∀ X0 X1 : G, (M.op (k X0 X1) X1) = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq225012 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq225012
    | exact resolve eq225012 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226808 : ∀ X0 X1 : G, (M.op (σ X1) X0) = X0 ∨ (M.op (σ X1) X0) = X0 ∨ (M.op (k (σ X1) X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq145905 (σ X0) X1
       have i₂ := eq225012 X0 X1
       grind)
    | exact superpose eq225012 eq145905
    | (have j0 := eq145905 (σ X1) X0
       have j1 := eq225012 X1 X0
       grind)
    | exact resolve eq145905 eq225012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145905
  have eq226878 : ∀ X0 X1 : G, (M.op (k (σ X1) X0) X0) = X0 ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq226808 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226808
  have eq227404 : ∀ X0 X1 : G, (k X0 (k X1 X0)) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2468 (k X0 X1) X1
       have i₂ := eq226555 X0 X1
       grind)
    | exact superpose eq226555 eq2468
    | (have j1 := eq226555 (k X1 X0) X0
       grind)
    | exact resolve eq2468 eq226555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226555
  have eq228219 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) X0) ∨ (σ X1) = (k (σ X1) X0) ∨ (M.op (k (σ X1) X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq227404 (σ X1) X0
       have i₂ := eq225012 X1 X0
       grind)
    | exact superpose eq225012 eq227404
    | (have j0 := eq227404 (σ X1) X0
       have j1 := eq225012 X1 X0
       grind)
    | exact resolve eq227404 eq225012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225012 eq227404
  have eq228510 : ∀ X0 X1 : G, (M.op (k (σ X1) X0) X0) = X0 ∨ (σ X1) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq228219 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228219
  have eq247768 : ∀ X0 X1 : G, (M.op (k X0 X1) X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq228510 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq228510
    | exact resolve eq228510 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228510
  have eq249114 : ∀ X0 X1 : G, (k X1 X0) = (k (k X1 X0) X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2465 (k X1 X0) X0
       have i₂ := eq247768 X1 X0
       grind)
    | exact superpose eq247768 eq2465
    | (have j1 := eq247768 (k X1 X0) X0
       grind)
    | exact resolve eq2465 eq247768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2465 eq247768
  have eq250344 : ∀ X0 X1 : G, (k X1 (τ X0)) = (k (M.op (τ X0) X1) (τ X0)) ∨ (k X1 (τ X0)) = X1 ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq249114 (τ X0) X1
       have i₂ := eq1319 X1 X0 X0
       grind)
    | exact superpose eq1319 eq249114
    | (have j0 := eq249114 (τ X0) X1
       have j1 := eq1319 X1 X0 x
       grind)
    | exact resolve eq249114 eq1319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319 eq249114
  have eq250547 : ∀ X0 X1 : G, (k X1 (τ X0)) = (k (M.op (τ X0) X1) (τ X0)) ∨ (k X1 (τ X0)) = X1 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq250344 X0 X1
       have j1 := eq13 X1 (τ X0)
       grind)
    | (have r₁ := eq250344 X0 X0
       have r₂ := eq13 X0 (τ X0)
       grind)
    | (have r₁ := eq250344 X0 X1
       have r₂ := eq13 (τ X0) (τ X0)
       grind)
    | exact resolve eq250344 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250344
  have eq250590 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k X1 (τ X0)) = X1 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq250547 X0 X1
       have i₂ := eq2468 (τ X0) X1
       grind)
    | exact superpose eq2468 eq250547
    | (have j0 := eq250547 X0 X1
       grind)
    | exact resolve eq250547 eq2468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2468 eq250547
  have eq250604 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq250590 X0 X1
       have j1 := eq12 X1 (τ X0)
       grind)
    | (have r₁ := eq250590 X0 X1
       have r₂ := eq12 X0 (τ X0)
       grind)
    | exact resolve eq250590 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250590
  have eq278664 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq250604 X0 X1
       grind)
    | exact superpose eq250604 eq18
    | (have j1 := eq250604 X0 X1
       grind)
    | exact resolve eq18 eq250604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq250604
  have eq333783 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq278664 X1 (τ X0)
       grind)
    | exact superpose eq278664 eq17
    | (have j1 := eq278664 X1 (τ X0)
       grind)
    | exact resolve eq17 eq278664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq278664
  have eq333893 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq333783 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq333783
    | (have j0 := eq333783 X0 X1
       grind)
    | exact resolve eq333783 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333783
  have eq334092 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq333893 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq333893
    | (have j0 := eq333893 X0 X1
       grind)
    | exact resolve eq333893 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333893
  have eq334240 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X1) (τ X0))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq334092 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq334092
    | (have j0 := eq334092 X0 X1
       grind)
    | exact resolve eq334092 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334092
  have eq336671 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X1) (τ X0))
       have i₂ := eq334240 X0 X1
       grind)
    | exact superpose eq334240 eq10
    | (have j1 := eq334240 X0 X1
       grind)
    | exact resolve eq10 eq334240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334240
  have eq341758 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (k X1 (σ X0))) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq336671 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq336671
    | (have j0 := eq336671 X1 (σ X0)
       grind)
    | exact resolve eq336671 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336671
  have eq342705 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (M.op X0 (τ X1)) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq341758 X0 X1
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq341758
    | (have j0 := eq341758 X0 X1
       grind)
    | exact resolve eq341758 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq341758
  have eq350997 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq226878 (σ X1) X0
       have i₂ := eq342705 X1 (σ X0)
       grind)
    | exact superpose eq342705 eq226878
    | (have j0 := eq226878 (σ X1) X0
       have j1 := eq342705 X1 (σ X0)
       grind)
    | exact resolve eq226878 eq342705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226878 eq342705
  have eq351047 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq350997 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350997
  have eq351115 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq351047 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq351047
    | (have j0 := eq351047 X0 X1
       grind)
    | exact resolve eq351047 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351047
  have eq384390 : ∀ X0 X1 : G, (M.op (τ (τ (σ X0))) X1) = X1 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq36455 X1 (σ X0)
       have i₂ := eq351115 (σ X1) X0
       grind)
    | exact superpose eq351115 eq36455
    | (have j1 := eq351115 (σ X1) X0
       grind)
    | exact resolve eq36455 eq351115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36455 eq351115
  have eq384859 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq384390 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq384390
    | (have j0 := eq384390 X0 X1
       grind)
    | exact resolve eq384390 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384390
  have eq407320 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq384859 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq384859
    | (have j0 := eq384859 (σ X0) X1
       grind)
    | exact resolve eq384859 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384859
  have eq407940 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq407320 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq407320
    | (have j0 := eq407320 X0 X1
       grind)
    | exact resolve eq407320 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407320
  have eq439719 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq407940 x y
       grind)
    | exact superpose eq407940 eq16
    | (have j1 := eq407940 x y
       grind)
    | exact resolve eq16 eq407940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407940
  have eq440476 : y = (M.op x y) := by
    first
    | (have j1 := eq160251 x y
       grind)
    | (have r₁ := eq439719
       have r₂ := eq160251 x y
       grind)
    | exact resolve eq439719 eq160251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160251 eq439719
  have eq441629 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq34268 x y
       have i₂ := eq440476
       grind)
    | exact superpose eq440476 eq34268
    | exact resolve eq34268 eq440476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34268
  have eq444368 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq441629
       grind)
    | exact superpose eq441629 eq16
    | exact resolve eq16 eq441629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441629
  have eq444872 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq444368
       have i₂ := eq440476
       grind)
    | exact superpose eq440476 eq444368
    | exact resolve eq444368 eq440476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440476 eq444368
  have eq444873 : False := by grind
  exact eq444873

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_x_pxx_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq33 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (M.op X0 X1) X0
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq33
    | exact resolve eq33 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq9
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq56 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 (k (τ X0) X1) X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq28
    | exact resolve eq28 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq70 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op X0 X0) = X0 := by
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
  clear eq17
  have eq71 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
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
  have eq97 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq37 X1 X2 X0
       grind)
    | exact superpose eq37 eq33
    | exact resolve eq33 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq68 x y
       grind)
    | exact superpose eq68 eq16
    | (have j1 := eq68 x y
       grind)
    | exact resolve eq16 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq68 X0 X0
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq68 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq68 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq68 X0 X1
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq68 X1 X0
       grind)
    | exact superpose eq68 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq68 X1 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq68 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq68 X0 X1
       grind)
    | exact resolve eq13 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (σ X1) (σ X0)
       have i₂ := eq68 X1 X0
       grind)
    | exact superpose eq68 eq33
    | (have j1 := eq68 X1 X1
       grind)
    | exact resolve eq33 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq179 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq169 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq180 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq167 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq181 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq179 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq179 X0 X1
       have r₂ := eq13 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq179 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq179 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq182 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq180 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq180 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq180 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq185 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq181 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq181
    | (have j0 := eq181 X0 X1
       grind)
    | exact resolve eq181 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq190 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq182 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq182
    | (have j0 := eq182 (τ X0) X1
       grind)
    | exact resolve eq182 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq192 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq190 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq190
    | (have j0 := eq190 X0 X1
       grind)
    | exact resolve eq190 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq195 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq192 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq192
    | (have j0 := eq192 X0 X1
       grind)
    | exact resolve eq192 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq552 : ∀ X0 X1 X2 : G, (τ (k (k X0 (σ X1)) X2)) = (k (M.op X1 (τ X0)) (τ X2)) ∨ (M.op X1 (τ X0)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 (M.op X1 (τ X0)) X2
       have i₂ := eq70 X1 X0
       grind)
    | exact superpose eq70 eq28
    | (have j1 := eq70 X1 X0
       grind)
    | exact resolve eq28 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq70
  have eq559 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (k (M.op X1 (τ X0)) (τ X2)) ∨ (M.op X1 (τ X0)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq552 X0 X1 X2
       have i₂ := eq56 X0 X1 X2
       grind)
    | exact superpose eq56 eq552
    | (have j0 := eq552 X0 X1 X2
       grind)
    | exact resolve eq552 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq552
  have eq1291 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq166
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq166
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq166 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq1292 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq1291
  have eq1690 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq172 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq1691 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1690 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1690
  have eq1714 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ (k (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1691 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1691
    | exact resolve eq1691 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1728 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ X0)) X1) = X1 ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq37 (σ X0) (σ X0) X1
       have i₂ := eq1691 X0
       grind)
    | exact superpose eq1691 eq37
    | (have j1 := eq1691 X0
       grind)
    | exact resolve eq37 eq1691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1691
  have eq1772 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1728 X0 X1
       have i₂ := eq33 (σ X0) X1
       grind)
    | exact superpose eq33 eq1728
    | (have j0 := eq1728 X0 X1
       grind)
    | exact resolve eq1728 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1728
  have eq1778 : ∀ X0 : G, (M.op (k (σ (τ X0)) X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1714 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1714
    | (have j0 := eq1714 X0
       grind)
    | exact resolve eq1714 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1714
  have eq1780 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1778 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1778
    | (have j0 := eq1778 X0
       grind)
    | exact resolve eq1778 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1778
  have eq1789 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq33 (k X0 X0) X0
       have i₂ := eq1780 X0
       grind)
    | exact superpose eq1780 eq33
    | (have j1 := eq1780 X0
       grind)
    | exact resolve eq33 eq1780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1780
  have eq1949 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0 (k (τ X0) (τ X0))
       have i₂ := eq1789 (τ X0)
       grind)
    | exact superpose eq1789 eq71
    | (have j0 := eq71 X0 (τ X0)
       have j1 := eq1789 (τ X0)
       grind)
    | exact resolve eq71 eq1789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq1789
  have eq1950 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq1949 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1949
  have eq1953 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq1950 X0
       have j1 := eq12 (σ (k (τ X0) (τ X0))) X0
       grind)
    | (have r₁ := eq1950 X0
       have r₂ := eq12 X0 (τ X0)
       grind)
    | exact resolve eq1950 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1950
  have eq1954 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1953 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1953
    | (have j0 := eq1953 X0
       grind)
    | exact resolve eq1953 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1953
  have eq1955 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1954 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1954
    | (have j0 := eq1954 X0
       grind)
    | exact resolve eq1954 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1954
  have eq1956 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1955 X0
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq1955
    | (have j0 := eq1955 X0
       grind)
    | exact resolve eq1955 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1955
  have eq4654 : ∀ X0 X1 : G, (M.op (σ (k (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1772 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1772
    | (have j0 := eq1772 (k (τ X0) (τ X0)) X0
       grind)
    | exact resolve eq1772 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1772
  have eq4714 : ∀ X0 X1 : G, (M.op (k (σ (τ X0)) X0) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4654 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq4654
    | (have j0 := eq4654 (k (σ (τ X0)) X0) X0
       grind)
    | exact resolve eq4654 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4654
  have eq4724 : ∀ X0 X1 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4714 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4714
    | (have j0 := eq4714 (k X0 X0) X0
       grind)
    | exact resolve eq4714 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4714
  have eq4946 : ∀ X0 X1 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 (k X0 X0) X0
       have i₂ := eq4724 X0 X1
       grind)
    | exact superpose eq4724 eq33
    | (have j1 := eq4724 X0 (k X0 X0)
       grind)
    | exact resolve eq33 eq4724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4724
  have eq5062 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq4946 X0 (k X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4946
  have eq5063 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq5062 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5062
  have eq5265 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq33 X0 (k X0 X0)
       have i₂ := eq5063 X0
       grind)
    | exact superpose eq5063 eq33
    | exact resolve eq33 eq5063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5063
  have eq5336 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5265 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq5265
    | exact resolve eq5265 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5265
  have eq10402 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (τ (σ X0)) = (τ (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1956 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq1956
    | exact resolve eq1956 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10425 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq22 (k (σ X0) (σ X0)) X0
       have i₂ := eq1956 (σ X0)
       grind)
    | exact superpose eq1956 eq22
    | (have j1 := eq1956 (σ X0)
       grind)
    | exact resolve eq22 eq1956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1956
  have eq10463 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10425 x
       have i₂ := eq22 (σ x) x
       grind)
    | exact superpose eq22 eq10425
    | (have j0 := eq10425 X0
       grind)
    | exact resolve eq10425 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10425
  have eq10478 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (τ (σ X0)) = (τ (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10402 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq10402
    | (have j0 := eq10402 X0
       grind)
    | exact resolve eq10402 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10402
  have eq10498 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10463 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10463
    | (have j0 := eq10463 X0
       grind)
    | exact resolve eq10463 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10463
  have eq10512 : ∀ X0 : G, (τ (σ X0)) = (k X0 X0) ∨ (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq10478 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq10478
    | (have j0 := eq10478 X0
       grind)
    | exact resolve eq10478 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10478
  have eq10531 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq10498 X0
       have i₂ := eq22 (σ X0) X0
       grind)
    | exact superpose eq22 eq10498
    | (have j0 := eq10498 X0
       grind)
    | exact resolve eq10498 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10498
  have eq10545 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10512 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10512
    | (have j0 := eq10512 X0
       grind)
    | exact resolve eq10512 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10512
  have eq10559 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq10531 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10531
    | (have j0 := eq10531 X0
       grind)
    | exact resolve eq10531 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10531
  have eq10585 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq10559 X0
       have j1 := eq195 X0 (k X0 X0)
       grind)
    | (have r₁ := eq10559 X0
       have r₂ := eq195 X0 x
       grind)
    | exact resolve eq10559 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq10559
  have eq10630 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10585 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq10585
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq10585 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10680 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq10630 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10630
  have eq10715 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq10680 X0
       have j1 := eq12 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq10680 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq10680 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10680
  have eq10815 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq10715 (τ X0)
       grind)
    | exact superpose eq10715 eq18
    | exact resolve eq18 eq10715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18738 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (σ (k (M.op (τ X0) (τ X0)) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq10545 (τ X0)
       have i₂ := eq559 X0 (τ X0) X0
       grind)
    | exact superpose eq559 eq10545
    | (have j0 := eq10545 (τ X0)
       have j1 := eq559 X0 (τ X0) x
       grind)
    | exact resolve eq10545 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10545
  have eq18739 : ∀ X0 : G, (k (τ X0) (τ X0)) = (k (M.op (τ X0) (τ X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq10585 (τ X0)
       have i₂ := eq559 X0 (τ X0) X0
       grind)
    | exact superpose eq559 eq10585
    | (have j1 := eq559 X0 (τ X0) x
       grind)
    | exact resolve eq10585 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559 eq10585
  have eq18779 : ∀ X0 : G, (k (τ X0) (τ X0)) = (k (M.op (τ X0) (τ X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq18739 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18739
  have eq18780 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (σ (k (M.op (τ X0) (τ X0)) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq18738 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18738
  have eq18800 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18779 X0
       have i₂ := eq10715 (τ X0)
       grind)
    | exact superpose eq10715 eq18779
    | (have j0 := eq18779 X0
       grind)
    | exact resolve eq18779 eq10715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10715 eq18779
  have eq18801 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (σ (k (M.op (τ X0) (τ X0)) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq18780 X0
       have j1 := eq12 (τ X0) (τ X0)
       grind)
    | (have r₁ := eq18780 X0
       have r₂ := eq12 X0 (τ X0)
       grind)
    | exact resolve eq18780 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18780
  have eq18822 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq18800 X0
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq18800
    | (have j0 := eq18800 X0
       grind)
    | exact resolve eq18800 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18800
  have eq18823 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18801 X0
       have i₂ := eq18 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq18 eq18801
    | (have j0 := eq18801 X0
       grind)
    | exact resolve eq18801 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18801
  have eq18832 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18823 X0
       have i₂ := eq10815 X0
       grind)
    | exact superpose eq10815 eq18823
    | (have j0 := eq18823 X0
       grind)
    | exact resolve eq18823 eq10815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10815 eq18823
  have eq18838 : ∀ X0 : G, (k (σ (τ X0)) X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18832 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq18832
    | (have j0 := eq18832 X0
       grind)
    | exact resolve eq18832 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq18832
  have eq18844 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18838 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18838
    | (have j0 := eq18838 X0
       grind)
    | exact resolve eq18838 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18838
  have eq18846 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq18844 X0
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq18844
    | (have j0 := eq18844 X0
       grind)
    | exact resolve eq18844 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq18844
  have eq20439 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq35 x y
       have i₂ := eq1292
       grind)
    | exact superpose eq1292 eq35
    | exact resolve eq35 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292
  have eq20504 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq20439
  have eq25288 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq18846 X0
       grind)
    | exact superpose eq18846 eq10
    | (have j1 := eq18846 X0
       grind)
    | exact resolve eq10 eq18846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18846
  have eq58075 : ∀ X0 : G, (σ (τ X0)) = (k X0 X0) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq25288 X0
       grind)
    | exact superpose eq25288 eq11
    | (have j1 := eq25288 X0
       grind)
    | exact resolve eq11 eq25288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58191 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq58075 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq58075
    | (have j0 := eq58075 X0
       grind)
    | exact resolve eq58075 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58075
  have eq58238 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq58191 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq58191
    | (have j0 := eq58191 (σ X0)
       grind)
    | exact resolve eq58191 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58191
  have eq58540 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq58238 X0
       have i₂ := eq22 (σ X0) X0
       grind)
    | exact superpose eq22 eq58238
    | (have j0 := eq58238 X0
       grind)
    | exact resolve eq58238 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58238
  have eq58565 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq58540 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq58540
    | (have j0 := eq58540 X0
       grind)
    | exact resolve eq58540 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58540
  have eq58567 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq58565 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq58565
    | (have j0 := eq58565 X0
       grind)
    | exact resolve eq58565 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58565
  have eq58865 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq185 X0 X0
       have i₂ := eq58567 X0
       grind)
    | exact superpose eq58567 eq185
    | (have j0 := eq185 X0 X0
       have j1 := eq58567 X0
       grind)
    | (have r₁ := eq185 X0 X0
       have r₂ := eq58567 X0
       grind)
    | exact resolve eq185 eq58567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq58567
  have eq59003 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq58865 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58865
  have eq59004 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq59003 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59003
  have eq61676 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) (σ X0)) = (M.op X1 (M.op (M.op (σ X0) X1) (σ X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (σ X0) (σ X0)
       have i₂ := eq59004 X0
       grind)
    | exact superpose eq59004 eq97
    | (have j1 := eq59004 X0
       grind)
    | exact resolve eq97 eq59004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq59004
  have eq61805 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq61676 X0 X1
       have i₂ := eq33 (σ X0) X1
       grind)
    | exact superpose eq33 eq61676
    | (have j0 := eq61676 X0 X1
       grind)
    | exact resolve eq61676 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61676
  have eq62168 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5336 X0
       have i₂ := eq61805 X0 X1
       grind)
    | exact superpose eq61805 eq5336
    | (have j1 := eq61805 X0 (σ (M.op X0 X0))
       grind)
    | exact resolve eq5336 eq61805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5336 eq61805
  have eq142120 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq62168 X0 (σ (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62168
  have eq142121 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq142120 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142120
  have eq142861 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37 (σ (M.op X0 X0)) (σ X0) X1
       have i₂ := eq142121 X0
       grind)
    | exact superpose eq142121 eq37
    | exact resolve eq37 eq142121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142121
  have eq234115 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq18822 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18822
  have eq234123 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq234115 X0
       have j1 := eq25288 X0
       grind)
    | (have r₁ := eq234115 X0
       have r₂ := eq25288 X0
       grind)
    | exact resolve eq234115 eq25288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25288 eq234115
  have eq234799 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq234123 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq234123
    | exact resolve eq234123 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234123
  have eq235410 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq234799 X0
       have i₂ := eq22 (σ X0) X0
       grind)
    | exact superpose eq22 eq234799
    | exact resolve eq234799 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq234799
  have eq235479 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq235410 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq235410
    | exact resolve eq235410 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235410
  have eq235893 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq235479 (σ X0)
       grind)
    | exact superpose eq235479 eq15
    | exact resolve eq15 eq235479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236033 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq235893 X0
       have i₂ := eq235479 X0
       grind)
    | exact superpose eq235479 eq235893
    | exact resolve eq235893 eq235479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235479 eq235893
  have eq456821 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq35 (σ x) (σ y)
       have i₂ := eq20504
       grind)
    | exact superpose eq20504 eq35
    | exact resolve eq35 eq20504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq20504
  have eq457030 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq456821
  have eq457239 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq457030
       have i₂ := eq236033 x
       grind)
    | exact superpose eq236033 eq457030
    | exact resolve eq457030 eq236033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236033 eq457030
  have eq457671 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq457239
       grind)
    | exact superpose eq457239 eq10
    | exact resolve eq10 eq457239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457239
  have eq458195 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq457671
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq457671
    | exact resolve eq457671 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457671
  have eq458196 : x = (M.op x x) := by grind
  clear eq458195
  have eq458307 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq142861 x X0
       have i₂ := eq458196
       grind)
    | exact superpose eq458196 eq142861
    | exact resolve eq142861 eq458196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142861
  have eq458415 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq37 x x X0
       have i₂ := eq458196
       grind)
    | exact superpose eq458196 eq37
    | exact resolve eq37 eq458196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq458196
  have eq458697 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq458415 X0
       have i₂ := eq33 x X0
       grind)
    | exact superpose eq33 eq458415
    | exact resolve eq458415 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458415
  have eq458791 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq458307 X0
       have i₂ := eq33 (σ x) X0
       grind)
    | exact superpose eq33 eq458307
    | exact resolve eq458307 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq458307
  have eq469704 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq458791 (σ y)
       grind)
    | exact superpose eq458791 eq16
    | exact resolve eq16 eq458791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458791
  have eq470280 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq469704
       have i₂ := eq458697 y
       grind)
    | exact superpose eq458697 eq469704
    | exact resolve eq469704 eq458697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458697 eq469704
  have eq470281 : False := by grind
  exact eq470281

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_x_pyy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq27 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq33
    | exact resolve eq33 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (M.op X0 X1) X0
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq33
    | exact resolve eq33 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq9
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq68 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq71 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
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
  have eq97 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq37 X1 X2 X0
       grind)
    | exact superpose eq37 eq33
    | exact resolve eq33 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq68 x y
       grind)
    | exact superpose eq68 eq16
    | (have j1 := eq68 x y
       grind)
    | exact resolve eq16 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq68 X0 X0
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq68 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq68 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq68 X0 X1
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (σ X1) (σ X0)
       have i₂ := eq68 X1 X0
       grind)
    | exact superpose eq68 eq33
    | (have j1 := eq68 X1 X1
       grind)
    | exact resolve eq33 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq68 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq178 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq177 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq180 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq167 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq182 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq180 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq180 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq180 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq190 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq182 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq182
    | (have j0 := eq182 (τ X0) X1
       grind)
    | exact resolve eq182 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq192 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq190 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq190
    | (have j0 := eq190 X0 X1
       grind)
    | exact resolve eq190 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq195 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq192 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq192
    | (have j0 := eq192 X0 X1
       grind)
    | exact resolve eq192 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq259 : ∀ X0 X1 X2 : G, (σ (k (k X1 (τ X0)) X2)) = (k (M.op X0 (σ X1)) (σ X2)) ∨ (M.op X0 (σ X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 X1 X0 X2
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq27
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq27 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq280 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq178
    | (have j0 := eq178 X0
       have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq178 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq285 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq280 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq1159 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq166
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq166
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq166 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq1160 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq1159
  have eq1356 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq172 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq1357 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1356 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1356
  have eq1381 : ∀ X0 : G, (M.op (σ (k (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1357 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1357
    | exact resolve eq1357 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357
  have eq1424 : ∀ X0 : G, (M.op (k (σ (τ X0)) X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1381 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1381
    | (have j0 := eq1381 X0
       grind)
    | exact resolve eq1381 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381
  have eq1428 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1424 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1424
    | (have j0 := eq1424 X0
       grind)
    | exact resolve eq1424 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1424
  have eq1436 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op X0 X1) (k X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (k X0 X0) X0
       have i₂ := eq1428 X0
       grind)
    | exact superpose eq1428 eq9
    | (have j1 := eq1428 X0
       grind)
    | exact resolve eq9 eq1428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1440 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq33 (k X0 X0) X0
       have i₂ := eq1428 X0
       grind)
    | exact superpose eq1428 eq33
    | (have j1 := eq1428 X0
       grind)
    | exact resolve eq33 eq1428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428
  have eq1565 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0 (k (τ X0) (τ X0))
       have i₂ := eq1440 (τ X0)
       grind)
    | exact superpose eq1440 eq71
    | (have j0 := eq71 X0 (τ X0)
       have j1 := eq1440 (τ X0)
       grind)
    | exact resolve eq71 eq1440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq1440
  have eq1566 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq1565 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1565
  have eq1570 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq1566 X0
       have j1 := eq12 (σ (k (τ X0) (τ X0))) X0
       grind)
    | (have r₁ := eq1566 X0
       have r₂ := eq12 X0 (τ X0)
       grind)
    | exact resolve eq1566 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1566
  have eq1571 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1570 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1570
    | (have j0 := eq1570 X0
       grind)
    | exact resolve eq1570 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1570
  have eq1572 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1571 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1571
    | (have j0 := eq1571 X0
       grind)
    | exact resolve eq1571 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1571
  have eq1573 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1572 X0
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq1572
    | (have j0 := eq1572 X0
       grind)
    | exact resolve eq1572 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq1572
  have eq1588 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op X1 (M.op (M.op X0 X1) X0)) ∨ (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq97 X0 X0 X0
       have i₂ := eq1436 X0 X1
       grind)
    | exact superpose eq1436 eq97
    | (have j1 := eq1436 X0 X2
       grind)
    | exact resolve eq97 eq1436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq1436
  have eq1630 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1588 X0 X1 X2
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq1588
    | (have j0 := eq1588 X0 X1 X2
       grind)
    | exact resolve eq1588 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1588
  have eq1755 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq22 (k (σ X0) (σ X0)) X0
       have i₂ := eq1573 (σ X0)
       grind)
    | exact superpose eq1573 eq22
    | (have j1 := eq1573 (σ X0)
       grind)
    | exact resolve eq22 eq1573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1573
  have eq1763 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1755 x
       have i₂ := eq22 (σ x) x
       grind)
    | exact superpose eq22 eq1755
    | (have j0 := eq1755 X0
       grind)
    | exact resolve eq1755 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1755
  have eq1780 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1763 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1763
    | (have j0 := eq1763 X0
       grind)
    | exact resolve eq1763 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1763
  have eq1795 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1780 X0
       have i₂ := eq22 (σ X0) X0
       grind)
    | exact superpose eq22 eq1780
    | (have j0 := eq1780 X0
       grind)
    | exact resolve eq1780 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1780
  have eq1809 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1795 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1795
    | (have j0 := eq1795 X0
       grind)
    | exact resolve eq1795 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1795
  have eq1822 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq1809 X0
       have j1 := eq195 X0 (k X0 X0)
       grind)
    | (have r₁ := eq1809 X0
       have r₂ := eq195 X0 x
       grind)
    | exact resolve eq1809 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq1809
  have eq1897 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1822 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq1822
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq1822 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1920 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1897 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1897
  have eq1937 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq1920 X0
       have j1 := eq12 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq1920 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq1920 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1920
  have eq2453 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1630 X0 (M.op (M.op X0 X0) (k X0 X0)) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1630
  have eq2454 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2453 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2453
  have eq2542 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34 (k X0 X0) X0 X0
       have i₂ := eq2454 X0
       grind)
    | exact superpose eq2454 eq34
    | exact resolve eq34 eq2454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq2454
  have eq2603 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2542 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq2542
    | exact resolve eq2542 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2542
  have eq2798 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (k X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37 (σ (k X0 X0)) (σ X0) X1
       have i₂ := eq2603 X0
       grind)
    | exact superpose eq2603 eq37
    | exact resolve eq37 eq2603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2603
  have eq20268 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 (τ (σ X0))) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1937 (σ X0)
       have i₂ := eq259 (σ X0) X0 X0
       grind)
    | exact superpose eq259 eq1937
    | (have j1 := eq259 (σ X0) X0 x
       grind)
    | exact resolve eq1937 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq20291 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 (τ (σ X0))) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq20268 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20268
  have eq20301 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq20291 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20291
    | (have j0 := eq20291 X0
       grind)
    | exact resolve eq20291 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20291
  have eq20411 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq20301 X0
       have i₂ := eq1822 X0
       grind)
    | exact superpose eq1822 eq20301
    | (have j0 := eq20301 X0
       grind)
    | exact resolve eq20301 eq1822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1822 eq20301
  have eq20498 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1937 (σ X0)
       have i₂ := eq20411 X0
       grind)
    | exact superpose eq20411 eq1937
    | (have j1 := eq20411 X0
       grind)
    | exact resolve eq1937 eq20411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1937
  have eq20575 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq20411 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20411
  have eq20602 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq20498 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq20498
    | (have j0 := eq20498 X0
       grind)
    | exact resolve eq20498 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20498
  have eq20612 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq20602 X0
       have j1 := eq20575 X0
       grind)
    | (have r₁ := eq20602 X0
       have r₂ := eq20575 X0
       grind)
    | exact resolve eq20602 eq20575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20575 eq20602
  have eq20617 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq20612 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20612
    | exact resolve eq20612 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20804 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq20617 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq20617
    | exact resolve eq20617 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq20617
  have eq20824 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq20804 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20804
    | exact resolve eq20804 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20804
  have eq21052 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2798 X0 X1
       have i₂ := eq20824 X0
       grind)
    | exact superpose eq20824 eq2798
    | exact resolve eq2798 eq20824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2798
  have eq23409 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq35 x y
       have i₂ := eq1160
       grind)
    | exact superpose eq1160 eq35
    | exact resolve eq35 eq1160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160
  have eq23481 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23409
  have eq23550 : (σ x) = (σ (k x x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23481
       have i₂ := eq20612 x
       grind)
    | exact superpose eq20612 eq23481
    | exact resolve eq23481 eq20612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23481
  have eq23622 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq23550
       have i₂ := eq20824 x
       grind)
    | exact superpose eq20824 eq23550
    | exact resolve eq23550 eq20824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23550
  have eq530844 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq35 (σ x) (σ y)
       have i₂ := eq23622
       grind)
    | exact superpose eq23622 eq35
    | exact resolve eq35 eq23622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq23622
  have eq531322 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq285 x
       grind)
    | (have r₁ := eq530844
       have r₂ := eq285 x
       grind)
    | exact resolve eq530844 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285 eq530844
  have eq531446 : (σ x) = (σ (k x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq531322
       have i₂ := eq20612 x
       grind)
    | exact superpose eq20612 eq531322
    | exact resolve eq531322 eq20612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20612 eq531322
  have eq531528 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq531446
       have i₂ := eq20824 x
       grind)
    | exact superpose eq20824 eq531446
    | exact resolve eq531446 eq20824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20824 eq531446
  have eq531592 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq531528
       grind)
    | exact superpose eq531528 eq10
    | exact resolve eq10 eq531528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531528
  have eq532102 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq531592
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq531592
    | exact resolve eq531592 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531592
  have eq532103 : x = (M.op x x) := by grind
  clear eq532102
  have eq532261 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq21052 x X0
       have i₂ := eq532103
       grind)
    | exact superpose eq532103 eq21052
    | exact resolve eq21052 eq532103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21052
  have eq532520 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq37 x x X0
       have i₂ := eq532103
       grind)
    | exact superpose eq532103 eq37
    | exact resolve eq37 eq532103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq532103
  have eq532830 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq532520 X0
       have i₂ := eq33 x X0
       grind)
    | exact superpose eq33 eq532520
    | exact resolve eq532520 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532520
  have eq533057 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq532261 X0
       have i₂ := eq33 (σ x) X0
       grind)
    | exact superpose eq33 eq532261
    | exact resolve eq532261 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq532261
  have eq542839 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq533057 (σ y)
       grind)
    | exact superpose eq533057 eq16
    | exact resolve eq16 eq533057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533057
  have eq543623 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq542839
       have i₂ := eq532830 y
       grind)
    | exact superpose eq532830 eq542839
    | exact resolve eq542839 eq532830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532830 eq542839
  have eq543624 : False := by grind
  exact eq543624

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_x_pxy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq22 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
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
  have eq34 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (M.op X0 X1) X0
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq34
    | exact resolve eq34 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq9
    | exact resolve eq9 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq46 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq45 X0
       have i₂ := eq34 (τ X0) (τ X0)
       grind)
    | exact superpose eq34 eq45
    | (have j0 := eq45 X0
       grind)
    | exact resolve eq45 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq47 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq46
    | (have j0 := eq46 X0
       grind)
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq48 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq74 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq76 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (M.op X0 X0) = X0 := by
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
  have eq93 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X1) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq38 (M.op (M.op (M.op X1 X2) X0) X1) X0 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq38
    | exact resolve eq38 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq38 X1 X2 X0
       grind)
    | exact superpose eq38 eq34
    | exact resolve eq34 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq74 x y
       grind)
    | exact superpose eq74 eq16
    | (have j1 := eq74 x y
       grind)
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq180 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (σ X1) (σ X0)
       have i₂ := eq74 X1 X0
       grind)
    | exact superpose eq74 eq34
    | (have j1 := eq74 X1 X1
       grind)
    | exact resolve eq34 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq74 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq185 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq189 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq175 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq191 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq189 X0
       have j1 := eq186 X0
       grind)
    | (have r₁ := eq189 X0
       have r₂ := eq186 X0
       grind)
    | exact resolve eq189 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq194 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq191 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq191
    | (have j0 := eq191 X0
       grind)
    | exact resolve eq191 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq456 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq23 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0
       have i₂ := eq47 (σ X0)
       grind)
    | exact superpose eq47 eq23
    | (have j1 := eq47 (σ X0)
       grind)
    | exact resolve eq23 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq463 : ∀ X0 : G, (τ (σ X0)) = (k (M.op (τ (σ X0)) (τ (σ X0))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq456 X0
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq456
    | (have j0 := eq456 X0
       grind)
    | exact resolve eq456 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq479 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq463 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq463
    | (have j0 := eq463 X0
       grind)
    | exact resolve eq463 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq492 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq479 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq479
    | (have j0 := eq479 X0
       grind)
    | exact resolve eq479 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq501 : ∀ X0 : G, (σ X0) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq492 (σ x)
       have i₂ := eq74 x x
       grind)
    | exact superpose eq74 eq492
    | (have j0 := eq492 (σ X0)
       have j1 := eq74 X0 X0
       grind)
    | exact resolve eq492 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq514 : ∀ X0 : G, (σ X0) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq501 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501
  have eq523 : ∀ X0 : G, (σ X0) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq514 X0
       have j1 := eq186 X0
       grind)
    | (have r₁ := eq514 X0
       have r₂ := eq186 X0
       grind)
    | exact resolve eq514 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq524 : ∀ X0 : G, (σ X0) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq523 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq523
    | (have j0 := eq523 X0
       grind)
    | exact resolve eq523 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq719 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq76
    | (have j0 := eq76 X1 X1
       grind)
    | exact resolve eq76 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq732 : ∀ X0 : G, (k (k X0 (σ (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq76 (τ X0) X0
       grind)
    | exact superpose eq76 eq47
    | (have j0 := eq47 X0
       have j1 := eq76 (τ X0) X0
       grind)
    | exact resolve eq47 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq76
  have eq752 : ∀ X0 : G, (k (k X0 (σ (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq732 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq758 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq752 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq752
    | (have j0 := eq752 X0
       grind)
    | exact resolve eq752 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq767 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq719 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq719
    | (have j0 := eq719 X1 X1
       grind)
    | exact resolve eq719 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq889 : ∀ X0 : G, (M.op (σ (τ (k X0 X0))) (σ (τ X0))) = (σ (k (τ (k X0 X0)) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq194 (τ X0)
       have i₂ := eq48 X0 X0
       grind)
    | exact superpose eq48 eq194
    | (have j0 := eq194 (τ X0)
       grind)
    | exact resolve eq194 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq906 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (M.op (σ (k (k X0 X0) X0)) (M.op (σ (k X0 X0)) X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 (σ (k X0 X0)) X1 (σ X0)
       have i₂ := eq194 X0
       grind)
    | exact superpose eq194 eq38
    | (have j1 := eq194 X0
       grind)
    | exact resolve eq38 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq922 : ∀ X0 : G, (M.op (σ (τ (k X0 X0))) (σ (τ X0))) = (k (σ (τ (k X0 X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq889 X0
       have i₂ := eq19 X0 (τ (k X0 X0))
       grind)
    | exact superpose eq19 eq889
    | (have j0 := eq889 X0
       grind)
    | exact resolve eq889 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889
  have eq927 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq922 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq922
    | (have j0 := eq922 X0
       grind)
    | exact resolve eq922 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq931 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq927 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq927
    | (have j0 := eq927 X0
       grind)
    | exact resolve eq927 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq935 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq931 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq931
    | (have j0 := eq931 X0
       grind)
    | exact resolve eq931 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931
  have eq939 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ X0) = (k (k (σ X0) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq758 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq758
    | (have j0 := eq758 (σ X0)
       grind)
    | exact resolve eq758 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq973 : ∀ X0 : G, (σ X0) = (σ (k (k (τ (σ X0)) X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq939 X0
       have i₂ := eq22 (σ X0) X0 X0
       grind)
    | exact superpose eq22 eq939
    | (have j0 := eq939 X0
       grind)
    | exact resolve eq939 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq939
  have eq974 : ∀ X0 : G, (σ X0) = (σ (k (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq973 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq973
    | (have j0 := eq973 X0
       grind)
    | exact resolve eq973 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973
  have eq1564 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq174
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq174
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq174 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq1565 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq1564
  have eq1682 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ X1) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ (k X1 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq180 X0 X1
       have i₂ := eq74 X1 X1
       grind)
    | exact superpose eq74 eq180
    | (have j0 := eq180 X0 X0
       have j1 := eq74 X0 X0
       grind)
    | exact resolve eq180 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1684 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k X1 (σ X0)) = X1 ∨ (σ X2) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (k X2 X0)) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq180 X2 X0
       grind)
    | exact superpose eq180 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq180 X2 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq180 X0 X1
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq180 X0 X0
       grind)
    | exact resolve eq12 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1709 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (k X2 X0)) (σ X0)) ∨ (σ X2) = (M.op (σ X0) (σ X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq1684 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1684
  have eq1710 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ X1) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ (k X1 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1682 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1682
  have eq1722 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (k X1 X0)) (σ X0)) ∨ (σ X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1710 X0 X1
       have j1 := eq186 X0
       grind)
    | (have r₁ := eq1710 X0 X1
       have r₂ := eq186 X0
       grind)
    | (have r₁ := eq1710 X0 X0
       have r₂ := eq186 X0
       grind)
    | (have r₁ := eq1710 X0 (k (k X0 X0) (k X0 X0))
       have r₂ := eq186 (k X0 X0)
       grind)
    | exact resolve eq1710 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq1710
  have eq4323 : ∀ X0 : G, (σ X0) = (σ (M.op (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq974 X0
       have i₂ := eq935 X0
       grind)
    | exact superpose eq935 eq974
    | (have j0 := eq974 X0
       have j1 := eq935 X0
       grind)
    | exact resolve eq974 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935 eq974
  have eq4366 : ∀ X0 : G, (σ X0) = (σ (M.op (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq4323 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4323
  have eq4472 : ∀ X0 : G, (τ (σ X0)) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (k X0 X0) X0)
       have i₂ := eq4366 X0
       grind)
    | exact superpose eq4366 eq10
    | (have j1 := eq4366 X0
       grind)
    | exact resolve eq10 eq4366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4366
  have eq4516 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4472 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4472
    | (have j0 := eq4472 X0
       grind)
    | exact resolve eq4472 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4472
  have eq4529 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op X0 X1) (k X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (k X0 X0) X0
       have i₂ := eq4516 X0
       grind)
    | exact superpose eq4516 eq9
    | (have j1 := eq4516 X0
       grind)
    | exact resolve eq9 eq4516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4516
  have eq4624 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq767 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq11112 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op X1 (M.op (M.op X0 X1) X0)) ∨ (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq100 X0 X0 X0
       have i₂ := eq4529 X0 X1
       grind)
    | exact superpose eq4529 eq100
    | (have j1 := eq4529 X0 X2
       grind)
    | exact resolve eq100 eq4529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4529
  have eq11165 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11112 X0 X1 X2
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq11112
    | (have j0 := eq11112 X0 X1 X2
       grind)
    | exact resolve eq11112 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11112
  have eq12247 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11165 X0 (M.op (M.op X0 X0) (k X0 X0)) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11165
  have eq12248 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12247 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12247
  have eq12279 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (k X0 X0) X0 X0
       have i₂ := eq12248 X0
       grind)
    | exact superpose eq12248 eq9
    | exact resolve eq9 eq12248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12281 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq35 (k X0 X0) X0 X0
       have i₂ := eq12248 X0
       grind)
    | exact superpose eq12248 eq35
    | exact resolve eq35 eq12248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12248
  have eq12643 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq12281 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq12281
    | exact resolve eq12281 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12281
  have eq12698 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq12279 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq12279
    | exact resolve eq12279 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12279
  have eq13157 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op (σ X0) X1) (σ (k X0 X0))) X2) X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq93 X1 (σ (k X0 X0)) (σ X0) X2
       have i₂ := eq12643 X0
       grind)
    | exact superpose eq12643 eq93
    | exact resolve eq93 eq12643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq12643
  have eq22115 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X1) (σ X0)) = (M.op X1 (M.op (M.op (σ X0) X1) (σ X0))) ∨ (σ X0) = (M.op (σ (k X2 X0)) (σ X0)) ∨ (σ X2) = (σ (k X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq100 X0 (σ X0) (σ X0)
       have i₂ := eq1722 X0 X1
       grind)
    | exact superpose eq1722 eq100
    | (have j1 := eq1722 X0 X2
       grind)
    | exact resolve eq100 eq1722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1722
  have eq22179 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (k X2 X0)) (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (σ X2) = (σ (k X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22115 X0 X1 X2
       have i₂ := eq34 (σ X0) X1
       grind)
    | exact superpose eq34 eq22115
    | (have j0 := eq22115 X0 X1 X2
       grind)
    | exact resolve eq22115 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22115
  have eq24046 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1709 X0 X1 (k X0 X0)
       have i₂ := eq524 X0
       grind)
    | exact superpose eq524 eq1709
    | (have j0 := eq1709 X0 X1 X0
       have j1 := eq524 X0
       grind)
    | exact resolve eq1709 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524 eq1709
  have eq24121 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq24046 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24046
  have eq24150 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq24121 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq24121 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq24121 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24121
  have eq24336 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24150 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24150
    | exact resolve eq24150 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24150
  have eq24546 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24336 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq24336
    | (have j0 := eq24336 X0 X1
       grind)
    | exact resolve eq24336 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24336
  have eq24574 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24546 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24546
    | (have j0 := eq24546 X0 X1
       grind)
    | exact resolve eq24546 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24546
  have eq26396 : x = (k y x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq492 x
       have i₂ := eq1565
       grind)
    | exact superpose eq1565 eq492
    | (have j0 := eq492 (σ x)
       grind)
    | exact resolve eq492 eq1565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq26478 : x ≠ y ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq1565
  have eq26498 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq26396
       have r₂ := eq26478
       grind)
    | exact resolve eq26396 eq26478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26396 eq26478
  have eq28303 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X1) (σ X0)) = (M.op X1 (M.op (M.op (σ X0) X1) (σ X0))) ∨ (σ X0) = (M.op (M.op (σ (k (k X0 X0) X0)) (M.op (σ (k X0 X0)) X2)) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq100 X0 (σ X0) (σ X0)
       have i₂ := eq906 X0 X1
       grind)
    | exact superpose eq906 eq100
    | (have j1 := eq906 X0 X2
       grind)
    | exact resolve eq100 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq28374 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ (k (k X0 X0) X0)) (M.op (σ (k X0 X0)) X2)) (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28303 X0 X1 X2
       have i₂ := eq34 (σ X0) X1
       grind)
    | exact superpose eq34 eq28303
    | (have j0 := eq28303 X0 X1 X2
       grind)
    | exact resolve eq28303 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28303
  have eq28549 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq4624 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4624
  have eq28786 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq28549 X0
       grind)
    | exact superpose eq28549 eq10
    | (have j1 := eq28549 X0
       grind)
    | exact resolve eq10 eq28549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28549
  have eq28865 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq28786 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq28786
    | (have j0 := eq28786 X0
       grind)
    | exact resolve eq28786 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28786
  have eq29069 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq28865 (σ X0)
       grind)
    | exact superpose eq28865 eq15
    | (have j1 := eq28865 (σ X0)
       grind)
    | exact resolve eq15 eq28865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28865
  have eq111042 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq29069 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29069
  have eq120379 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq111042 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq111042
    | exact resolve eq111042 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq111042
  have eq120421 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq120379 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq120379
    | (have j0 := eq120379 X0
       grind)
    | exact resolve eq120379 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120379
  have eq120451 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq120421 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq120421
    | (have j0 := eq120421 X0
       grind)
    | exact resolve eq120421 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120421
  have eq120475 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq120451 X0
       have j1 := eq24574 X0 x
       grind)
    | (have r₁ := eq120451 X0
       have r₂ := eq24574 X0 X0
       grind)
    | exact resolve eq120451 eq24574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24574 eq120451
  have eq120705 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq12698 X0
       have i₂ := eq120475 X0
       grind)
    | exact superpose eq120475 eq12698
    | exact resolve eq12698 eq120475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12698
  have eq120711 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X2) X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13157 X0 X1 X2
       have i₂ := eq120475 X0
       grind)
    | exact superpose eq120475 eq13157
    | exact resolve eq13157 eq120475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13157
  have eq120833 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq120475 (σ X0)
       grind)
    | exact superpose eq120475 eq15
    | exact resolve eq15 eq120475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120847 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq48 X0 X0
       have i₂ := eq120475 (τ X0)
       grind)
    | exact superpose eq120475 eq48
    | exact resolve eq48 eq120475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq120935 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq120847 X0
       have i₂ := eq120475 X0
       grind)
    | exact superpose eq120475 eq120847
    | exact resolve eq120847 eq120475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120847
  have eq120948 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq120833 X0
       have i₂ := eq120475 X0
       grind)
    | exact superpose eq120475 eq120833
    | exact resolve eq120833 eq120475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120833
  have eq745865 : ∀ X0 X1 : G, (σ X1) ≠ (σ X1) ∨ (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq22179 X1 (σ (k X0 X1)) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22179
  have eq745866 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq745865 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745865
  have eq745869 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq745866 X0 X1
       have i₂ := eq120475 X1
       grind)
    | exact superpose eq120475 eq745866
    | (have j0 := eq745866 X0 X1
       grind)
    | exact resolve eq745866 eq120475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745866
  have eq747887 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ (k X1 X0))) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (σ (k X1 X0)) (σ X0)
       have i₂ := eq745869 X1 X0
       grind)
    | exact superpose eq745869 eq34
    | (have j1 := eq745869 X1 X0
       grind)
    | exact resolve eq34 eq745869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745869
  have eq1144132 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq747887 x y
       have i₂ := eq26498
       grind)
    | exact superpose eq26498 eq747887
    | (have j0 := eq747887 x y
       grind)
    | exact resolve eq747887 eq26498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26498 eq747887
  have eq1144133 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq1144132
  have eq1144171 : (σ x) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1144133
       have i₂ := eq120948 x
       grind)
    | exact superpose eq120948 eq1144133
    | exact resolve eq1144133 eq120948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144133
  have eq1144195 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1144171
       have i₂ := eq120948 x
       grind)
    | exact superpose eq120948 eq1144171
    | exact resolve eq1144171 eq120948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120948 eq1144171
  have eq1144196 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq1144195
  have eq1146776 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (M.op (σ (k (k X0 X0) X0)) (M.op (σ (k X0 X0)) X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq28374 X0 (M.op (σ (k (k X0 X0) X0)) (M.op (σ (k X0 X0)) X1)) X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28374
  have eq1146777 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (k (k X0 X0) X0)) (M.op (σ (k X0 X0)) X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1146776 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146776
  have eq1146785 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (k (M.op X0 X0) X0)) (M.op (σ (M.op X0 X0)) X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1146777 X0 X1
       have i₂ := eq120475 X0
       grind)
    | exact superpose eq120475 eq1146777
    | exact resolve eq1146777 eq120475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120475 eq1146777
  have eq1175660 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op (k (σ (M.op (τ X0) (τ X0))) X0) (M.op (σ (M.op (τ X0) (τ X0))) X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1146785 (τ X0) X1
       have i₂ := eq19 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq19 eq1146785
    | exact resolve eq1146785 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1146785
  have eq1176961 : ∀ X0 X1 : G, (M.op (M.op (k (σ (M.op (τ X0) (τ X0))) X0) (M.op (σ (M.op (τ X0) (τ X0))) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1175660 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1175660
    | exact resolve eq1175660 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175660
  have eq1177204 : ∀ X0 X1 : G, (M.op (M.op (k (σ (τ (M.op X0 X0))) X0) (M.op (σ (τ (M.op X0 X0))) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1176961 X0 X1
       have i₂ := eq120935 X0
       grind)
    | exact superpose eq120935 eq1176961
    | exact resolve eq1176961 eq120935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120935 eq1176961
  have eq1177322 : ∀ X0 X1 : G, (M.op (M.op (k (M.op X0 X0) X0) (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1177204 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq1177204
    | exact resolve eq1177204 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177204
  have eq1177748 : ∀ X0 : G, (M.op (M.op (k (M.op X0 X0) X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1177322 X0 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq1177322
    | exact resolve eq1177322 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177322
  have eq1181985 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (k (M.op X0 X0) X0) X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38 (M.op (k (M.op X0 X0) X0) X0) X0 X1
       have i₂ := eq1177748 X0
       grind)
    | exact superpose eq1177748 eq38
    | exact resolve eq38 eq1177748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177748
  have eq1187505 : ∀ X0 X1 : G, (M.op (k (M.op X0 X0) X0) X1) = (M.op X0 (M.op (k (M.op X0 X0) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1181985 X0 (M.op (k (M.op X0 X0) X0) X1)
       have i₂ := eq38 (k (M.op X0 X0) X0) X1 X0
       grind)
    | exact superpose eq38 eq1181985
    | exact resolve eq1181985 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq1181985
  have eq1199547 : ∀ X0 X1 : G, (M.op (M.op (k (M.op X0 X0) X0) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (M.op (k (M.op X0 X0) X0) X1)
       have i₂ := eq1187505 X0 X1
       grind)
    | exact superpose eq1187505 eq34
    | exact resolve eq34 eq1187505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187505
  have eq1200573 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) (k (M.op X2 X2) X2)) X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1199547 X2 (M.op (M.op (M.op X0 X1) (k (M.op X2 X2) X2)) X0)
       have i₂ := eq35 (k (M.op X2 X2) X2) X0 X1
       grind)
    | exact superpose eq35 eq1199547
    | exact resolve eq1199547 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1200583 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (k (M.op X1 X1) X1)) (M.op X0 X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1199547 X1 (M.op (M.op X0 (k (M.op X1 X1) X1)) (M.op X0 X2))
       have i₂ := eq100 (k (M.op X1 X1) X1) X0 X2
       grind)
    | exact superpose eq100 eq1199547
    | exact resolve eq1199547 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq1199547
  have eq1218448 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) (k (M.op X1 X1) X1)) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1200573 (M.op (M.op (σ X0) (k (M.op X1 X1) X1)) (σ (M.op X0 X0))) (M.op (M.op (σ X0) (k (M.op X1 X1) X1)) (σ (M.op X0 X0))) X1
       have i₂ := eq120711 X0 (k (M.op X1 X1) X1) (M.op (M.op (σ X0) (k (M.op X1 X1) X1)) (σ (M.op X0 X0)))
       grind)
    | exact superpose eq120711 eq1200573
    | exact resolve eq1200573 eq120711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120711 eq1200573
  have eq1301275 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1144196
       grind)
    | exact superpose eq1144196 eq10
    | exact resolve eq10 eq1144196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144196
  have eq1301859 : (σ x) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1301275
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1301275
    | exact resolve eq1301275 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1301275
  have eq1304005 : (M.op x x) = (τ (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1301859
       grind)
    | exact superpose eq1301859 eq10
    | exact resolve eq10 eq1301859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1301859
  have eq1304579 : x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1304005
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1304005
    | exact resolve eq1304005 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304005
  have eq1304580 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq1304579
  have eq1304914 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq120705 x
       have i₂ := eq1304580
       grind)
    | exact superpose eq1304580 eq120705
    | exact resolve eq120705 eq1304580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120705
  have eq1305104 : y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq36 x x
       have i₂ := eq1304580
       grind)
    | exact superpose eq1304580 eq36
    | exact resolve eq36 eq1304580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1304580
  have eq1343646 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1304914
       grind)
    | exact superpose eq1304914 eq16
    | exact resolve eq16 eq1304914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304914
  have eq1346379 : (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1343646
       have i₂ := eq1305104
       grind)
    | exact superpose eq1305104 eq1343646
    | exact resolve eq1343646 eq1305104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1305104 eq1343646
  have eq1346384 : (σ y) ≠ (σ y) ∨ x = (M.op x x) := by grind
  clear eq1346379
  have eq1346385 : x = (M.op x x) := by grind
  clear eq1346384
  have eq1346715 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (k (M.op X0 X0) X0)) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1218448 x X0
       have i₂ := eq1346385
       grind)
    | exact superpose eq1346385 eq1218448
    | exact resolve eq1218448 eq1346385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218448
  have eq1347009 : ∀ X0 : G, (M.op (M.op (M.op x (k (M.op X0 X0) X0)) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1200583 x X0 x
       have i₂ := eq1346385
       grind)
    | exact superpose eq1346385 eq1200583
    | exact resolve eq1200583 eq1346385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200583 eq1346385
  have eq1347033 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1347009 X0
       have i₂ := eq34 x (k (M.op X0 X0) X0)
       grind)
    | exact superpose eq34 eq1347009
    | exact resolve eq1347009 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1347009
  have eq1347121 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1346715 X0
       have i₂ := eq34 (σ x) (k (M.op X0 X0) X0)
       grind)
    | exact superpose eq34 eq1346715
    | exact resolve eq1346715 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1346715
  have eq1367525 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1347121 (σ y)
       grind)
    | exact superpose eq1347121 eq16
    | exact resolve eq16 eq1347121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1347121
  have eq1368397 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1367525
       have i₂ := eq1347033 y
       grind)
    | exact superpose eq1347033 eq1367525
    | exact resolve eq1367525 eq1347033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1347033 eq1367525
  have eq1368398 : False := by grind
  exact eq1368398

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_pyx_pxy_Equation3180 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3180 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq57 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq57
    | (have j0 := eq57 (σ x) (σ y)
       grind)
    | exact resolve eq57 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq59 eq57
    | exact resolve eq57 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
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
  clear eq49
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq76
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq76
    | exact resolve eq76 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq81
    | exact resolve eq81 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq84 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X1)
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq12
    | (have j0 := eq12 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X1)
       have r₂ := eq57 X0 X1
       grind)
    | exact resolve eq12 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq66 eq12
    | (have j0 := eq12 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq66
       grind)
    | exact resolve eq12 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq92 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq89
  have eq95 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq105 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq113 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq125 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq113
       grind)
    | exact superpose eq113 eq16
    | exact resolve eq16 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq979 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ (k X0 X1)) X2) (σ X0)) X2) = X2 ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (σ X0) (σ X1)
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq14
    | (have j1 := eq68 X0 X1
       grind)
    | exact resolve eq14 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq16143 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq82 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq16144 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq16143
    | exact resolve eq16143 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16143
  have eq16155 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq16144
       have r₂ := eq28
       grind)
    | exact resolve eq16144 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16144
  have eq16460 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq16155 eq57
    | exact resolve eq57 eq16155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16155
  have eq16503 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq16460
    | exact resolve eq16460 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16460
  have eq16509 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq57 y x
       have i₂ := eq16503
       grind)
    | exact superpose eq16503 eq57
    | exact resolve eq57 eq16503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16514 : y = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq95 y x
       have i₂ := eq16503
       grind)
    | exact superpose eq16503 eq95
    | exact resolve eq95 eq16503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq16503
  have eq16549 : y = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16514
  have eq16552 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16509
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16509
    | exact resolve eq16509 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16509
  have eq16560 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq16552 eq92
    | exact resolve eq92 eq16552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq16552
  have eq16578 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq16560
  have eq16875 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq113
       have i₂ := eq16549
       grind)
    | exact superpose eq16549 eq113
    | exact resolve eq113 eq16549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq16885 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq979 y x X0
       have i₂ := eq16549
       grind)
    | exact superpose eq16549 eq979
    | (have j0 := eq979 y x x
       grind)
    | exact resolve eq979 eq16549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979 eq16549
  have eq16892 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16885 X0
       have i₂ := eq57 (σ y) X0
       grind)
    | exact superpose eq57 eq16885
    | exact resolve eq16885 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16885
  have eq16901 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16875
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16875
    | exact resolve eq16875 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16875
  have eq16904 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16892 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16892
    | (have j0 := eq16892 X0
       grind)
    | exact resolve eq16892 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16892
  have eq16910 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16904 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16904
    | (have j0 := eq16904 X0
       grind)
    | exact resolve eq16904 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16904
  have eq16914 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16910 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16910
    | (have j0 := eq16910 X0
       grind)
    | exact resolve eq16910 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16910
  have eq16918 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq16914
    | (have j0 := eq16914 X0
       grind)
    | exact resolve eq16914 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16914
  have eq16919 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq16918 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16918
  have eq16925 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16919 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16919
    | (have j0 := eq16919 X0
       grind)
    | exact resolve eq16919 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16919
  have eq16930 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16925 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16925
    | (have j0 := eq16925 X0
       grind)
    | exact resolve eq16925 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16925
  have eq16931 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16930 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16930
  have eq17370 : (τ (σ y)) = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq16578 eq125
    | exact resolve eq125 eq16578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq16578
  have eq17396 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq17370
    | exact resolve eq17370 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17370
  have eq18409 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16901 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq16901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16901
  have eq18416 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18409
  have eq18423 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq18416
    | exact resolve eq18416 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18416
  have eq18424 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18423
  have eq18825 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq17396
       grind)
    | exact superpose eq17396 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq17396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17396
  have eq18832 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq18825
  have eq18839 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18832
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18832
    | exact resolve eq18832 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18832
  have eq18840 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq18839
  have eq19051 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq18424 eq16931
    | exact resolve eq16931 eq18424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16931 eq18424
  have eq19100 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq19051
  have eq19156 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq19100 eq28
    | exact resolve eq28 eq19100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19100
  have eq20062 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq63 y x X0
       have i₂ := eq18840
       grind)
    | exact superpose eq18840 eq63
    | exact resolve eq63 eq18840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq20136 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq20062 X0
       have i₂ := eq57 y X0
       grind)
    | exact superpose eq57 eq20062
    | exact resolve eq20062 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq20062
  have eq20516 : x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18840
       have i₂ := eq20136 x
       grind)
    | exact superpose eq20136 eq18840
    | exact resolve eq18840 eq20136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18840 eq20136
  have eq20582 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq20516
  have eq20613 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20582 eq30
    | exact resolve eq30 eq20582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq20582
  have eq20743 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq20613
    | exact resolve eq20613 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20613
  have eq20744 : y = (M.op x y) ∨ x = y := by grind
  clear eq20743
  have eq20884 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq20744 eq21
    | exact resolve eq21 eq20744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21041 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq20884
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20884
    | exact resolve eq20884 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20884
  have eq21140 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq21041 eq19156
    | (have r₁ := eq19156
       have r₂ := eq21041
       grind)
    | exact resolve eq19156 eq21041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19156 eq21041
  have eq21149 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq21140
  have eq21150 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq21149
  have eq21235 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq21150 eq29
    | exact resolve eq29 eq21150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq21150
  have eq21413 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq21235
    | exact resolve eq21235 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq21235
  have eq21633 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq21413 eq20744
    | exact resolve eq20744 eq21413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20744 eq21413
  have eq21634 : x = y := by grind
  clear eq21633
  have eq21717 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq21634
       grind)
    | exact superpose eq21634 eq19
    | exact resolve eq19 eq21634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq21718 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq21634
       grind)
    | exact superpose eq21634 eq25
    | exact resolve eq25 eq21634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq21634
  have eq21836 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq21718
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21718
    | exact resolve eq21718 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq21718
  have eq21853 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21836 eq27
    | exact resolve eq27 eq21836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq21836
  have eq22131 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq21853 eq105
    | exact resolve eq105 eq21853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq21853
  have eq22210 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq22131
       have i₂ := eq21717
       grind)
    | exact superpose eq21717 eq22131
    | exact resolve eq22131 eq21717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21717 eq22131
  have eq22230 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22210 eq15
    | exact resolve eq15 eq22210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22210
  have eq22279 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq22230
    | exact resolve eq22230 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq22230
  have eq22288 : False := by grind
  exact eq22288

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_pyy_pyx_Equation3180 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq111 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq111 (M.op X0 X1) X0
       have i₂ := eq111 X0 X1
       grind)
    | exact superpose eq111 eq111
    | exact resolve eq111 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq121 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq115 (σ X0) (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq115
    | exact resolve eq115 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq406 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq408 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq411 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq406 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq406
    | (have j0 := eq406 X0 X1
       grind)
    | exact resolve eq406 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq560 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq411 x y
       grind)
    | exact superpose eq411 eq16
    | (have j1 := eq411 x y
       grind)
    | exact resolve eq16 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq12495 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq408 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq408
    | exact resolve eq408 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq12721 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12495 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq12495
    | (have j0 := eq12495 X0 X1
       grind)
    | exact resolve eq12495 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12495
  have eq13998 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq560
       have i₂ := eq12721 y x
       grind)
    | exact superpose eq12721 eq560
    | (have j1 := eq12721 y x
       grind)
    | (have r₁ := eq560
       have r₂ := eq12721 y x
       grind)
    | (have r₁ := eq560
       have r₂ := eq12721 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq560
       have r₂ := eq12721 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq560 eq12721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560 eq12721
  have eq13999 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq13998
  have eq21791 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13999
       grind)
    | exact superpose eq13999 eq16
    | exact resolve eq16 eq13999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13999
  have eq21792 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq21791
       have r₂ := eq23 x
       grind)
    | exact resolve eq21791 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21791
  have eq21794 : y = (τ (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq21792
       grind)
    | exact superpose eq21792 eq10
    | exact resolve eq10 eq21792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21792
  have eq21873 : x = y ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq21794
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq21794
    | exact resolve eq21794 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21794
  have eq22285 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21873
       grind)
    | exact superpose eq21873 eq16
    | exact resolve eq16 eq21873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21873
  have eq22286 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq22285
       have r₂ := eq23 x
       grind)
    | exact resolve eq22285 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq22285
  have eq22319 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq22286
       grind)
    | exact superpose eq22286 eq10
    | exact resolve eq10 eq22286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22286
  have eq22399 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq22319
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq22319
    | exact resolve eq22319 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22319
  have eq22400 : y = (M.op x x) := by grind
  clear eq22399
  have eq22406 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq121 x
       have i₂ := eq22400
       grind)
    | exact superpose eq22400 eq121
    | exact resolve eq121 eq22400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq22529 : y = (M.op x y) := by
    first
    | (have i₁ := eq115 x x
       have i₂ := eq22400
       grind)
    | exact superpose eq22400 eq115
    | exact resolve eq115 eq22400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq22400
  have eq22829 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22406
       grind)
    | exact superpose eq22406 eq16
    | exact resolve eq16 eq22406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22406
  have eq22895 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq22829
       have i₂ := eq22529
       grind)
    | exact superpose eq22529 eq22829
    | exact resolve eq22829 eq22529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22529 eq22829
  have eq22896 : False := by grind
  exact eq22896

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_y_pyx_Equation3180 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq111 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq111 (M.op X0 X1) X0
       have i₂ := eq111 X0 X1
       grind)
    | exact superpose eq111 eq111
    | exact resolve eq111 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq121 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq115 (σ X0) (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq115
    | exact resolve eq115 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq509 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq511 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq514 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq509 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq509
    | (have j0 := eq509 X0 X1
       grind)
    | exact resolve eq509 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq2189 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq514 x y
       grind)
    | exact superpose eq514 eq16
    | (have j1 := eq514 x y
       grind)
    | exact resolve eq16 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq29733 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq511 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq511
    | exact resolve eq511 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq29987 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29733 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq29733
    | (have j0 := eq29733 X0 X1
       grind)
    | exact resolve eq29733 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29733
  have eq44049 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq2189
       have i₂ := eq29987 y x
       grind)
    | exact superpose eq29987 eq2189
    | (have j1 := eq29987 y x
       grind)
    | (have r₁ := eq2189
       have r₂ := eq29987 y x
       grind)
    | (have r₁ := eq2189
       have r₂ := eq29987 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2189
       have r₂ := eq29987 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2189 eq29987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2189 eq29987
  have eq44050 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq44049
  have eq66556 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq44050
       grind)
    | exact superpose eq44050 eq16
    | exact resolve eq16 eq44050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44050
  have eq66557 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq66556
       have r₂ := eq23 x
       grind)
    | exact resolve eq66556 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66556
  have eq66559 : y = (τ (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq66557
       grind)
    | exact superpose eq66557 eq10
    | exact resolve eq10 eq66557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66557
  have eq66652 : x = y ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq66559
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq66559
    | exact resolve eq66559 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66559
  have eq66654 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66652
       grind)
    | exact superpose eq66652 eq16
    | exact resolve eq16 eq66652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66652
  have eq66655 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq66654
       have r₂ := eq23 x
       grind)
    | exact resolve eq66654 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq66654
  have eq66703 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq66655
       grind)
    | exact superpose eq66655 eq10
    | exact resolve eq10 eq66655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66655
  have eq66796 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq66703
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq66703
    | exact resolve eq66703 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66703
  have eq66797 : y = (M.op x x) := by grind
  clear eq66796
  have eq66803 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq121 x
       have i₂ := eq66797
       grind)
    | exact superpose eq66797 eq121
    | exact resolve eq121 eq66797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq67094 : y = (M.op x y) := by
    first
    | (have i₁ := eq115 x x
       have i₂ := eq66797
       grind)
    | exact superpose eq66797 eq115
    | exact resolve eq115 eq66797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq66797
  have eq67409 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66803
       grind)
    | exact superpose eq66803 eq16
    | exact resolve eq16 eq66803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66803
  have eq67478 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq67409
       have i₂ := eq67094
       grind)
    | exact superpose eq67094 eq67409
    | exact resolve eq67409 eq67094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67094 eq67409
  have eq67479 : False := by grind
  exact eq67479

/-- `Equation3263`: `x ◇ x = x ◇ (y ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pxy_y_pxy_Equation3263 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3263 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3263.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
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
  have eq78 : y ≠ (M.op x y) ∨ y = (M.op y x) ∨ y = (k x y) := by
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
  have eq79 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq97 x y
       grind)
    | exact superpose eq97 eq44
    | (have j1 := eq97 x y
       grind)
    | exact resolve eq44 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq109
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq109
    | exact resolve eq109 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq122 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq120
    | exact resolve eq120 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq123 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq122
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq122
    | exact resolve eq122 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq123 eq97
    | (have j0 := eq97 (σ x) (σ y)
       grind)
    | exact resolve eq97 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq126
    | exact resolve eq126 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq130 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq127
       have r₂ := eq27
       grind)
    | exact resolve eq127 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq132 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq130
    | exact resolve eq130 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq134 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq132 eq27
    | exact resolve eq27 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq132 eq79
    | (have r₁ := eq79
       have r₂ := eq132
       grind)
    | exact resolve eq79 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq132
  have eq557 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq556
  have eq1316 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq557 eq123
    | exact resolve eq123 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq1320 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq1316
  have eq1325 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1320
       have r₂ := eq134
       grind)
    | exact resolve eq1320 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq1320
  have eq1329 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1325 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1325
       grind)
    | exact resolve eq13 eq1325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325
  have eq1335 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1329
  have eq1336 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1335
    | exact resolve eq1335 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335
  have eq1343 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1336 eq123
    | exact resolve eq123 eq1336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq1336
  have eq1346 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1343
  have eq1350 : y = (M.op x y) := by
    first
    | (have r₁ := eq1346
       have r₂ := eq27
       grind)
    | exact resolve eq1346 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346
  have eq1352 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1350 eq20
    | exact resolve eq20 eq1350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1357 : y ≠ y ∨ y = (M.op y x) ∨ y = (k x y) := by
    first
    | exact superpose eq1350 eq78
    | (have r₁ := eq78
       have r₂ := eq1350
       grind)
    | exact resolve eq78 eq1350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq1361 : y = (k x y) ∨ y = (M.op y x) := by grind
  clear eq1357
  have eq1368 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1352
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1352
    | exact resolve eq1352 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1352
  have eq1370 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1368 eq26
    | exact resolve eq26 eq1368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2508 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1361
       grind)
    | exact superpose eq1361 eq44
    | exact resolve eq44 eq1361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1361
  have eq2515 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1368 eq2508
    | exact resolve eq2508 eq1368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2508
  have eq2517 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2515
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2515
    | exact resolve eq2515 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2515
  have eq2518 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1368 eq2517
    | exact resolve eq2517 eq1368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2517
  have eq2522 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2518 eq97
    | (have j0 := eq97 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq97 eq2518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2518
  have eq2523 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by grind
  clear eq2522
  have eq2525 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1370 eq2523
    | exact resolve eq2523 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2523
  have eq2528 : y = (M.op y x) := by
    first
    | (have r₁ := eq2525
       have r₂ := eq27
       grind)
    | exact resolve eq2525 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2525
  have eq2533 : y ≠ y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq2528
       grind)
    | exact superpose eq2528 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2528
       grind)
    | exact resolve eq13 eq2528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2528
  have eq2540 : (M.op x y) = (k x y) := by grind
  clear eq2533
  have eq2544 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq2540
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2540
    | exact resolve eq2540 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2540
  have eq2547 : y = (k x y) := by
    first
    | exact superpose eq1350 eq2544
    | exact resolve eq2544 eq1350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1350 eq2544
  have eq2553 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq2547
       grind)
    | exact superpose eq2547 eq44
    | exact resolve eq44 eq2547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq2547
  have eq2560 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1368 eq2553
    | exact resolve eq2553 eq1368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2553
  have eq2562 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2560
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2560
    | exact resolve eq2560 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2560
  have eq2563 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1368 eq2562
    | exact resolve eq2562 eq1368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1368 eq2562
  have eq2566 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2563 eq97
    | (have j0 := eq97 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq97 eq2563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq2563
  have eq2567 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq2566
  have eq2569 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1370 eq2567
    | exact resolve eq2567 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370 eq2567
  have eq2572 : False := by grind
  exact eq2572
