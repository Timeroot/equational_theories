import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1031`: `x = x ◇ ((x ◇ (y ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_x_pxy_Equation1031 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1031 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1031.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq320 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq337 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq320 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq338 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq337 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq512 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq338 X1 X0
       grind)
    | exact superpose eq338 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq338 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq338 X0 X1
       grind)
    | exact resolve eq13 eq338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq524 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq338 (σ y) (σ x)
       grind)
    | exact superpose eq338 eq16
    | (have j1 := eq338 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq529 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq512 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq531 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq524
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq524
    | exact resolve eq524 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq533 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq529 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq529 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq529 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq569 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq533 X0 (τ X1)
       grind)
    | exact superpose eq533 eq18
    | (have j1 := eq533 X0 (τ X1)
       grind)
    | exact resolve eq18 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq586 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq533 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2055 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq569 (τ X0) X1
       grind)
    | exact superpose eq569 eq17
    | (have j1 := eq569 (τ X0) X1
       grind)
    | exact resolve eq17 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq569
  have eq2068 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2055 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2055
    | (have j0 := eq2055 X0 X1
       grind)
    | exact resolve eq2055 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2055
  have eq2088 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2068 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2068
    | (have j0 := eq2068 X0 X1
       grind)
    | exact resolve eq2068 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2068
  have eq2095 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2088 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2088
    | (have j0 := eq2088 X0 X1
       grind)
    | exact resolve eq2088 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2088
  have eq2174 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2095 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2095
    | (have j0 := eq2095 X1 (σ X0)
       grind)
    | exact resolve eq2095 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2095
  have eq2918 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq531
       have i₂ := eq338 y x
       grind)
    | exact superpose eq338 eq531
    | (have j1 := eq338 y x
       grind)
    | exact resolve eq531 eq338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2921 : (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq2918
  have eq2932 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2174 X0 X0
       have i₂ := eq533 X0 (σ X0)
       grind)
    | exact superpose eq533 eq2174
    | (have j0 := eq2174 X1 X0
       have j1 := eq533 X0 (σ X1)
       grind)
    | exact resolve eq2174 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533 eq2174
  have eq2993 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2932 X0 X1
       have j1 := eq586 X0 (σ X1)
       grind)
    | (have r₁ := eq2932 X0 X1
       have r₂ := eq586 X0 (σ X1)
       grind)
    | exact resolve eq2932 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586 eq2932
  have eq3388 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq2993 (σ X0) X1
       grind)
    | exact superpose eq2993 eq28
    | (have j1 := eq2993 (σ X0) X1
       grind)
    | exact resolve eq28 eq2993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2993
  have eq3414 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3388 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3388
    | (have j0 := eq3388 X0 X1
       grind)
    | exact resolve eq3388 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3388
  have eq3438 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3414 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3414
    | (have j0 := eq3414 X0 X1
       grind)
    | exact resolve eq3414 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3414
  have eq3450 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3438 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3438
    | (have j0 := eq3438 X0 X1
       grind)
    | exact resolve eq3438 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3438
  have eq3584 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3450 x y
       grind)
    | exact superpose eq3450 eq16
    | (have j1 := eq3450 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq3450 x y
       grind)
    | exact resolve eq16 eq3450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3450
  have eq3619 : x = (k x y) := by grind
  clear eq3584
  have eq4552 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2921
       have i₂ := eq3619
       grind)
    | exact superpose eq3619 eq2921
    | exact resolve eq2921 eq3619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2921
  have eq4562 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq531
       have i₂ := eq4552
       grind)
    | exact superpose eq4552 eq531
    | exact resolve eq531 eq4552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531 eq4552
  have eq4576 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4562
  have eq4577 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4576
       have i₂ := eq3619
       grind)
    | exact superpose eq3619 eq4576
    | exact resolve eq4576 eq3619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4576
  have eq4578 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4577
  have eq4581 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4578
       grind)
    | exact superpose eq4578 eq16
    | exact resolve eq16 eq4578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4578
  have eq4620 : (σ x) ≠ (σ x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq4581
       have i₂ := eq338 y x
       grind)
    | exact superpose eq338 eq4581
    | (have j1 := eq338 y x
       grind)
    | exact resolve eq4581 eq338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq4623 : (M.op x y) = (k x y) := by grind
  clear eq4620
  have eq4625 : x = (M.op x y) := by
    first
    | (have i₁ := eq4623
       have i₂ := eq3619
       grind)
    | exact superpose eq3619 eq4623
    | exact resolve eq4623 eq3619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3619 eq4623
  have eq4626 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq4581
       have i₂ := eq4625
       grind)
    | exact superpose eq4625 eq4581
    | exact resolve eq4581 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4581 eq4625
  have eq4642 : False := by grind
  exact eq4642

/-- `Equation1031`: `x = x ◇ ((x ◇ (y ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pxy_y_pxy_Equation1031 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1031 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1031.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (M.op X1 X2)) X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq63 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op X0 (M.op x x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, X0 ≠ X0 ∨ (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 X0) X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq63 X0
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq74 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq73 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq308 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq14 (M.op (M.op X1 X1) X0) X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq319 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq318 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq323 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq308 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq324 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq323 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq325 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq319 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq319 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq319 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq339 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq325 (σ X0)
       grind)
    | exact superpose eq325 eq15
    | exact resolve eq15 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq339 X0
       have i₂ := eq325 X0
       grind)
    | exact superpose eq325 eq339
    | exact resolve eq339 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325 eq339
  have eq407 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq74 (σ X0)
       have i₂ := eq358 X0
       grind)
    | exact superpose eq358 eq74
    | exact resolve eq74 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq407 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq407
    | exact resolve eq407 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq414 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq410 X0
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq410
    | exact resolve eq410 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq410
  have eq493 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq324 (σ X1) (σ X0)
       grind)
    | exact superpose eq324 eq15
    | (have j1 := eq324 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq501 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq324 X1 (τ X0)
       grind)
    | exact superpose eq324 eq18
    | (have j1 := eq324 X1 (τ X0)
       grind)
    | exact resolve eq18 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq324
  have eq510 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq493 X0 X1
       have i₂ := eq358 X1
       grind)
    | exact superpose eq358 eq493
    | (have j0 := eq493 X0 X1
       grind)
    | exact resolve eq493 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358 eq493
  have eq583 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq501 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq501
    | exact resolve eq501 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501
  have eq637 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq583 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq583
    | (have j0 := eq583 X0 X1
       grind)
    | exact resolve eq583 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq1380 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq510 x y
       grind)
    | exact superpose eq510 eq16
    | (have j1 := eq510 x y
       grind)
    | exact resolve eq16 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq1474 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1380
       have i₂ := eq637 x y
       grind)
    | exact superpose eq637 eq1380
    | (have j1 := eq637 x y
       grind)
    | (have r₁ := eq1380
       have r₂ := eq637 x y
       grind)
    | exact resolve eq1380 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637 eq1380
  have eq1475 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1474
  have eq1483 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq414 y
       have i₂ := eq1475
       grind)
    | exact superpose eq1475 eq414
    | exact resolve eq414 eq1475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475
  have eq1503 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1483
       have r₂ := eq16
       grind)
    | exact resolve eq1483 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1483
  have eq1510 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1503
       grind)
    | exact superpose eq1503 eq10
    | exact resolve eq10 eq1503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503
  have eq1557 : x = (M.op y y) := by
    first
    | (have i₁ := eq1510
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1510
    | exact resolve eq1510 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1510
  have eq1564 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq414 y
       have i₂ := eq1557
       grind)
    | exact superpose eq1557 eq414
    | exact resolve eq414 eq1557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414 eq1557
  have eq1585 : False := by grind
  exact eq1585

/-- `Equation1052`: `x = x ◇ ((y ◇ (y ◇ z)) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxx_x_pxy_Equation1052 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1052 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1052.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X2)) X1)) = X0 := by
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
  have eq176 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) X0
       have i₂ := eq176 X0 (M.op X0 X0)
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1041 : x ≠ (M.op x y) ∨ y = (M.op y y) ∨ x = (k x y) := by
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
  have eq1042 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1061 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq1062 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1106 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1107 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1108 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1107 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq1142 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1061
       grind)
    | exact superpose eq1061 eq40
    | exact resolve eq40 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061
  have eq1143 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1142
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1142
    | exact resolve eq1142 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142
  have eq1145 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1143
    | exact resolve eq1143 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq1153 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1145 eq1062
    | exact resolve eq1062 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1160 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1153
       have r₂ := eq27
       grind)
    | exact resolve eq1153 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153
  have eq1169 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1160 eq199
    | exact resolve eq199 eq1160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1174 : ∀ X0 : G, y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq1160 eq1169
    | exact resolve eq1169 eq1160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160 eq1169
  have eq1181 : ∀ X0 X1 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq199 y X1
       have i₂ := eq1174 X0
       grind)
    | exact superpose eq1174 eq199
    | (have j1 := eq1174 (σ x)
       grind)
    | exact resolve eq199 eq1174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1186 : ∀ X0 X1 : G, (M.op X1 (σ y)) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op X0 y) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1174 eq1181
    | (have j0 := eq1181 X0 X1
       have j1 := eq1174 X1
       grind)
    | exact resolve eq1181 eq1174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174 eq1181
  have eq1201 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq1186 (M.op sF2 sF3) x
       grind)
    | exact superpose eq1186 eq26
    | (have j1 := eq1186 x (σ x)
       grind)
    | exact resolve eq26 eq1186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186
  have eq1202 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1201 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201
  have eq1220 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1202 x
       grind)
    | exact superpose eq1202 eq18
    | (have j1 := eq1202 x
       grind)
    | exact resolve eq18 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202
  have eq1221 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1220
  have eq1225 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1221 eq1042
    | (have r₁ := eq1042
       have r₂ := eq1221
       grind)
    | exact resolve eq1042 eq1221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq1229 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1221 eq27
    | exact resolve eq27 eq1221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221
  have eq1230 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1225
  have eq1232 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1230 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq1230
       grind)
    | exact resolve eq13 eq1230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1238 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1232 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1232
  have eq1349 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1230
       have i₂ := eq1238 sF3
       grind)
    | exact superpose eq1238 eq1230
    | exact resolve eq1230 eq1238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230 eq1238
  have eq1352 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1349
  have eq1411 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1352 eq152
    | exact resolve eq152 eq1352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq1352
  have eq1416 : (σ x) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq1411
    | exact resolve eq1411 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1411
  have eq1421 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ y = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1416 eq1145
    | exact resolve eq1145 eq1416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145 eq1416
  have eq1427 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ y = (k y y) := by grind
  clear eq1421
  have eq1433 : x = (M.op x y) ∨ y = (M.op y y) ∨ y = (k y y) := by
    first
    | (have r₁ := eq1427
       have r₂ := eq1229
       grind)
    | exact resolve eq1427 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229 eq1427
  have eq1436 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq1108 y
       grind)
    | (have r₁ := eq1433
       have r₂ := eq1108 y
       grind)
    | exact resolve eq1433 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108 eq1433
  have eq1442 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq199 y x
       have i₂ := eq1436
       grind)
    | exact superpose eq1436 eq199
    | exact resolve eq199 eq1436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1452 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1436 eq1442
    | exact resolve eq1442 eq1436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1436 eq1442
  have eq1469 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1452 x
       grind)
    | exact superpose eq1452 eq18
    | (have j1 := eq1452 x
       grind)
    | exact resolve eq18 eq1452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1452
  have eq1470 : x = (M.op x y) := by grind
  clear eq1469
  have eq1477 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq1470
       grind)
    | exact superpose eq1470 eq22
    | exact resolve eq22 eq1470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1483 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op y y) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | (have i₁ := eq1041
       have i₂ := eq1470
       grind)
    | exact superpose eq1470 eq1041
    | (have r₁ := eq1041
       have r₂ := eq1470
       grind)
    | exact resolve eq1041 eq1470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041 eq1470
  have eq1484 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op y y) := by grind
  clear eq1483
  have eq1486 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1477 eq20
    | exact resolve eq20 eq1477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477
  have eq2138 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1484 eq40
    | exact resolve eq40 eq1484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484
  have eq2142 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq2138
    | exact resolve eq2138 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2138
  have eq2145 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1486 eq2142
    | exact resolve eq2142 eq1486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2142
  have eq2154 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2145 eq1062
    | exact resolve eq1062 eq2145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062 eq2145
  have eq2161 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq2154
  have eq2210 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq2161 eq199
    | exact resolve eq199 eq2161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2220 : ∀ X0 : G, y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq2161 eq2210
    | exact resolve eq2210 eq2161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2161 eq2210
  have eq2227 : ∀ X0 X1 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq199 y X1
       have i₂ := eq2220 X0
       grind)
    | exact superpose eq2220 eq199
    | (have j1 := eq2220 (σ x)
       grind)
    | exact resolve eq199 eq2220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2237 : ∀ X0 X1 : G, (M.op X1 (σ y)) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 y) = X0 := by
    intro X0 X1
    first
    | exact superpose eq2220 eq2227
    | (have j0 := eq2227 X0 X1
       have j1 := eq2220 X1
       grind)
    | exact resolve eq2227 eq2220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2220 eq2227
  have eq2257 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq2237 (M.op sF2 sF3) x
       grind)
    | exact superpose eq2237 eq26
    | (have j1 := eq2237 X0 (σ x)
       grind)
    | exact resolve eq26 eq2237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2237
  have eq2258 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2257 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2257
  have eq2267 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq2258 y
       grind)
    | exact superpose eq2258 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq2258 y
       grind)
    | exact resolve eq13 eq2258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2283 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2267 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2267
  have eq2339 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2258 y
       have i₂ := eq2283 y
       grind)
    | exact superpose eq2283 eq2258
    | exact resolve eq2258 eq2283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2258
  have eq2363 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2339
  have eq2414 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq2363
       grind)
    | exact superpose eq2363 eq40
    | exact resolve eq40 eq2363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq2363
  have eq2422 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2414
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2414
    | exact resolve eq2414 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2414
  have eq2429 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2422 eq1106
    | (have j0 := eq1106 (σ y) (σ y)
       grind)
    | (have r₁ := eq1106 (σ y) (σ y)
       have r₂ := eq2422
       grind)
    | exact resolve eq1106 eq2422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106 eq2422
  have eq2430 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2429
  have eq2431 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2430
  have eq2443 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2431 eq199
    | exact resolve eq199 eq2431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq2447 : (σ y) = (k (σ y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2431 eq2283
    | exact resolve eq2283 eq2431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2431
  have eq2451 : (σ y) = (k (σ y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2447
  have eq2456 : ∀ X0 : G, (M.op X0 (k (σ y) y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2283 eq2443
    | exact resolve eq2443 eq2283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2283 eq2443
  have eq2459 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2451 eq2456
    | exact resolve eq2456 eq2451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2451 eq2456
  have eq2487 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2459 eq26
    | (have j1 := eq2459 (σ x)
       grind)
    | exact resolve eq26 eq2459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2459
  have eq2488 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2487
  have eq2494 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq2488 eq27
    | exact resolve eq27 eq2488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2488
  have eq2500 : False := by grind
  exact eq2500

/-- `Equation1060`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_pxy_pyx_Equation1060 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1060 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1060.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X1)) = X0 := by
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
  have eq53 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X0 (M.op x X0))
       have i₂ := eq14 X0 X0 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X0) X1
       have i₂ := eq53 X0 (M.op X0 X0)
       grind)
    | exact superpose eq53 eq13
    | (have j0 := eq13 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X1
       have r₂ := eq53 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq83 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq83
  have eq95 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq96 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq98 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq11 sF3 (σ X0)
       grind)
    | exact superpose eq11 eq36
    | (have j1 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq36 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq95
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq95 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100
    | exact resolve eq100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq106
    | exact resolve eq106 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq108 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq96
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq96 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq16
    | exact resolve eq16 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq108
  have eq115 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq115 X1 (M.op X0 X0)
       have i₂ := eq53 X0 (M.op X0 X0)
       grind)
    | exact superpose eq53 eq115
    | (have j0 := eq115 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq115 X0 (M.op X0 X0)
       have r₂ := eq53 X0 (M.op X0 X0)
       grind)
    | exact resolve eq115 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq129 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq132 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq130 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq130
    | exact resolve eq130 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq147 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq148 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq149 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq196 : (σ (k (k (M.op x y) x) y)) = (k (k (σ (M.op x y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq147 eq40
    | exact resolve eq40 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq147
  have eq264 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (M.op X1 X1)
       have i₂ := eq132 X1 (τ X0)
       grind)
    | exact superpose eq132 eq34
    | exact resolve eq34 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq274 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq264 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq264
    | exact resolve eq264 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq363 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq592 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq79 X0 X0
       grind)
    | exact superpose eq79 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq79 X0 X0
       grind)
    | (have r₁ := eq13 (σ X1) X1
       have r₂ := eq79 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq13 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq595 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq115 X1 (σ X0)
       have i₂ := eq79 X0 X0
       grind)
    | exact superpose eq79 eq115
    | (have j0 := eq115 X1 (σ X0)
       have j1 := eq79 X0 X0
       grind)
    | (have r₁ := eq115 X0 (σ X1)
       have r₂ := eq79 X0 X1
       grind)
    | (have r₁ := eq115 X0 (σ X0)
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq115 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq606 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq595 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq609 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq592 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq610 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq606 X0 X1
       have j1 := eq115 X1 (σ X0)
       grind)
    | (have r₁ := eq606 X0 X1
       have r₂ := eq115 X0 (σ X0)
       grind)
    | exact resolve eq606 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq606
  have eq611 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq609 X0 X1
       have j1 := eq13 (σ X0) X1
       grind)
    | (have r₁ := eq609 X0 X1
       have r₂ := eq13 (σ X0) X1
       grind)
    | exact resolve eq609 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq7874 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ (M.op X0 X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq610 (M.op X0 X0) X1
       have i₂ := eq132 X0 (M.op X0 X0)
       grind)
    | exact superpose eq132 eq610
    | (have j0 := eq610 (M.op X0 X0) X1
       grind)
    | exact resolve eq610 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq7960 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq7874 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7874
  have eq7997 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7960 X0 X1
       have i₂ := eq274 X1 X0
       grind)
    | exact superpose eq274 eq7960
    | exact resolve eq7960 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7960
  have eq8302 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ (M.op X0 X0)) X1) = (k (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq611 (M.op X0 X0) X1
       have i₂ := eq132 X0 (M.op X0 X0)
       grind)
    | exact superpose eq132 eq611
    | (have j0 := eq611 (M.op X0 X0) X1
       grind)
    | exact resolve eq611 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq611
  have eq8388 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (k (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq8302 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8302
  have eq10323 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq80 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq80
    | (have j0 := eq80 x
       grind)
    | exact resolve eq80 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq10338 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq10323
  have eq10341 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10338
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq10338
    | exact resolve eq10338 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq10338
  have eq10356 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq10341
       have r₂ := eq13 (σ x) x
       grind)
    | exact resolve eq10341 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10341
  have eq10359 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq10356 eq49
    | exact resolve eq49 eq10356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq10613 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq98 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq98
    | (have j0 := eq98 y
       grind)
    | exact resolve eq98 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq10627 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq10613
  have eq10629 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq10627
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq10627
    | exact resolve eq10627 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq10627
  have eq10651 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq10629
       have r₂ := eq13 (σ y) x
       grind)
    | exact resolve eq10629 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10629
  have eq10686 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq10651 eq113
    | exact resolve eq113 eq10651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq11091 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq150
    | (have j0 := eq150 (M.op x y)
       grind)
    | exact resolve eq150 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq11104 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq11091
  have eq11105 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq149 eq11104
    | exact resolve eq11104 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq11104
  have eq11134 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq11105
       have r₂ := eq13 (σ (M.op x y)) x
       grind)
    | exact resolve eq11105 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11105
  have eq33054 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq10356 eq90
    | exact resolve eq90 eq10356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq10356
  have eq35201 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq10651 eq114
    | exact resolve eq114 eq10651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq10651
  have eq63214 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq33054
       grind)
    | exact superpose eq33054 eq16
    | exact resolve eq16 eq33054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33054
  have eq63296 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq10359 eq63214
    | exact resolve eq63214 eq10359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63214
  have eq63336 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq63296
       have r₂ := eq13 x x
       grind)
    | exact resolve eq63296 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63296
  have eq63639 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq35201
       grind)
    | exact superpose eq35201 eq16
    | exact resolve eq16 eq35201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35201
  have eq63721 : (M.op y y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq10686 eq63639
    | exact resolve eq63639 eq10686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63639
  have eq63761 : (M.op y y) = (k y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq63721
       have r₂ := eq13 y x
       grind)
    | exact resolve eq63721 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63721
  have eq82113 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq107 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq82114 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq82113
    | exact resolve eq82113 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82113
  have eq82119 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq82114
       have r₂ := eq27
       grind)
    | exact resolve eq82114 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82114
  have eq82122 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq82119 eq10686
    | exact resolve eq10686 eq82119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10686 eq82119
  have eq82248 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq82122
       have i₂ := eq63761
       grind)
    | exact superpose eq63761 eq82122
    | exact resolve eq82122 eq63761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63761 eq82122
  have eq82249 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq82248
    | exact resolve eq82248 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq82248
  have eq82250 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq82249
  have eq82252 : (τ (σ x)) = (k x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq82250 eq10359
    | exact resolve eq10359 eq82250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10359 eq82250
  have eq82378 : (τ (σ x)) = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq82252
       have i₂ := eq63336
       grind)
    | exact superpose eq63336 eq82252
    | exact resolve eq82252 eq63336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63336 eq82252
  have eq82379 : x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq82378
    | exact resolve eq82378 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq82378
  have eq82380 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq82379
  have eq82384 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 y X0
       have i₂ := eq82380
       grind)
    | exact superpose eq82380 eq53
    | exact resolve eq53 eq82380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82425 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq7997 y X0
       have i₂ := eq82380
       grind)
    | exact superpose eq82380 eq7997
    | exact resolve eq7997 eq82380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82380
  have eq82503 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq82425 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq82425
    | (have j0 := eq82425 X0
       grind)
    | exact resolve eq82425 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq82425
  have eq82517 : ∀ X0 X1 : G, (M.op X1 y) = X1 ∨ (M.op X0 x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq53 x X0
       have i₂ := eq82384 X1
       grind)
    | exact superpose eq82384 eq53
    | (have j1 := eq82384 X1
       grind)
    | exact resolve eq53 eq82384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82384
  have eq82783 : ∀ X0 X1 : G, (M.op X1 (σ y)) = X1 ∨ (M.op X0 x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq53 x X0
       have i₂ := eq82503 X1
       grind)
    | exact superpose eq82503 eq53
    | (have j1 := eq82503 X1
       grind)
    | exact resolve eq53 eq82503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq82503
  have eq83046 : ∀ X0 : G, (M.op X0 x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq82517 X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq82517
    | (have j0 := eq82517 X0 x
       grind)
    | exact resolve eq82517 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82517
  have eq83378 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq74 x x
       have i₂ := eq83046 x
       grind)
    | exact superpose eq83046 eq74
    | exact resolve eq74 eq83046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83433 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8388 x x
       have i₂ := eq83046 x
       grind)
    | exact superpose eq83046 eq8388
    | exact resolve eq8388 eq83046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8388 eq83046
  have eq83651 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq83433 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq83433
    | (have j0 := eq83433 X0
       grind)
    | exact resolve eq83433 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83433
  have eq92602 : ∀ X0 : G, (M.op X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq82783
    | (have j0 := eq82783 X0 (σ x)
       grind)
    | exact resolve eq82783 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92946 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq274 X0 x
       have i₂ := eq92602 x
       grind)
    | exact superpose eq92602 eq274
    | exact resolve eq274 eq92602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq92983 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq7997 x X0
       have i₂ := eq92602 x
       grind)
    | exact superpose eq92602 eq7997
    | exact resolve eq7997 eq92602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7997 eq92602
  have eq93235 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq92983 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq92983
    | (have j0 := eq92983 X0
       grind)
    | exact resolve eq92983 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92983
  have eq93244 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq92946 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq92946
    | (have j0 := eq92946 X0
       grind)
    | exact resolve eq92946 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92946
  have eq105841 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq83378 y
       grind)
    | exact superpose eq83378 eq44
    | exact resolve eq44 eq83378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83378
  have eq105902 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq105841
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq105841
    | exact resolve eq105841 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105841
  have eq105972 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq105902
    | exact resolve eq105902 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105902
  have eq108785 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq83651 eq105972
    | exact resolve eq105972 eq83651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83651 eq105972
  have eq108793 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq108785
  have eq108824 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq108793
    | exact resolve eq108793 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108793
  have eq108863 : x = (M.op x y) := by
    first
    | (have r₁ := eq108824
       have r₂ := eq27
       grind)
    | exact resolve eq108824 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108824
  have eq108865 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq108863 eq20
    | exact resolve eq20 eq108863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109046 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq108865
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq108865
    | exact resolve eq108865 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq108865
  have eq109117 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq109046 eq26
    | exact resolve eq26 eq109046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq109167 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = X0 ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq109046 eq93235
    | exact resolve eq93235 eq109046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93235
  have eq109170 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq109046 eq93244
    | exact resolve eq93244 eq109046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93244
  have eq109183 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq109170 X0
       grind)
    | (have r₁ := eq109170 X0
       have r₂ := eq27
       grind)
    | exact resolve eq109170 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109170
  have eq109186 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq109167 X0
       grind)
    | (have r₁ := eq109167 X0
       have r₂ := eq27
       grind)
    | exact resolve eq109167 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109167
  have eq110502 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq109117 eq82783
    | (have j0 := eq82783 X0 x
       grind)
    | exact resolve eq82783 eq109117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82783
  have eq110525 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq110502 X0
       grind)
    | (have r₁ := eq110502 X0
       have r₂ := eq27
       grind)
    | exact resolve eq110502 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110502
  have eq110629 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq109183 eq363
    | exact resolve eq363 eq109183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363 eq109183
  have eq110706 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq30 eq110629
    | exact resolve eq110629 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq110629
  have eq110753 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) := by
    intro X0
    first
    | exact superpose eq108863 eq110706
    | exact resolve eq110706 eq108863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108863 eq110706
  have eq110782 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq110753 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq110753
    | exact resolve eq110753 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110753
  have eq111222 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq74 x x
       have i₂ := eq110525 x
       grind)
    | exact superpose eq110525 eq74
    | exact resolve eq74 eq110525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110525
  have eq114460 : (σ (k (M.op x y) y)) = (k (k (σ (M.op x y)) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq196
       have i₂ := eq110782 sF0
       grind)
    | exact superpose eq110782 eq196
    | exact resolve eq196 eq110782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq110782
  have eq114631 : (σ (k (M.op x y) y)) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq109046 eq114460
    | exact resolve eq114460 eq109046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114460
  have eq114697 : (σ (k (M.op x y) y)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq11134 eq114631
    | exact resolve eq114631 eq11134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11134 eq114631
  have eq114745 : (σ (k (M.op x y) y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq114697
       have i₂ := eq74 sF1 sF3
       grind)
    | exact superpose eq74 eq114697
    | exact resolve eq114697 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq114697
  have eq114777 : (M.op (σ (M.op x y)) (σ y)) = (σ (k (M.op x y) y)) := by
    first
    | exact superpose eq109186 eq114745
    | exact resolve eq114745 eq109186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109186 eq114745
  have eq114798 : (M.op (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq148 eq114777
    | exact resolve eq114777 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq114777
  have eq114812 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq109117 eq114798
    | exact resolve eq114798 eq109117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109117 eq114798
  have eq133068 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq111222 y
       grind)
    | exact superpose eq111222 eq44
    | exact resolve eq44 eq111222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq111222
  have eq133126 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq109046 eq133068
    | exact resolve eq133068 eq109046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109046 eq133068
  have eq133238 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq114812 eq133126
    | exact resolve eq133126 eq114812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114812 eq133126
  have eq133308 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq133238
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq133238
    | exact resolve eq133238 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq133238
  have eq133358 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq133308
    | exact resolve eq133308 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq133308
  have eq133394 : False := by grind
  exact eq133394

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation1061 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1061 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq46 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq60 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq46 (σ X0)
       grind)
    | exact superpose eq46 eq15
    | exact resolve eq15 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq60
    | exact resolve eq60 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq60
  have eq83 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq83 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq83
    | (have j0 := eq83 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq83 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq84 x y
       grind)
    | exact superpose eq84 eq16
    | (have j1 := eq84 x y
       grind)
    | exact resolve eq16 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq373 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq235
       have i₂ := eq83 x y
       grind)
    | exact superpose eq83 eq235
    | (have j1 := eq83 (σ x) (σ y)
       grind)
    | (have r₁ := eq235
       have r₂ := eq83 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq235
       have r₂ := eq83 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq235 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq235
  have eq374 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq373
  have eq375 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq374
       grind)
    | exact superpose eq374 eq16
    | exact resolve eq16 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq376 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq375
       have r₂ := eq69 x
       grind)
    | exact resolve eq375 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq410 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq376
       grind)
    | exact superpose eq376 eq10
    | exact resolve eq10 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq427 : x = y := by
    first
    | (have i₁ := eq410
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq410
    | exact resolve eq410 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq475 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq427
       grind)
    | exact superpose eq427 eq16
    | exact resolve eq16 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq476 : False := by grind
  exact eq476

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyx_pxy_Equation1061 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1061 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
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
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ x) (σ y)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq14 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq14 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13 (σ y) (σ x)
       grind)
    | exact superpose eq13 eq16
    | (have j1 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq13 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq13 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq19
    | exact resolve eq19 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq21 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq18
    | exact resolve eq18 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq22 : (M.op (σ x) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by grind
  clear eq20
  have eq23 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by grind
  clear eq21
  have eq24 : (M.op (σ x) (σ x)) ≠ (σ (k y y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq22
    | exact resolve eq22 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq25 : (M.op (σ x) (σ x)) = (σ (k y y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq23
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq23
    | exact resolve eq23 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq26 : (σ (k y y)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by grind
  clear eq24
  have eq27 : (σ (k y y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by grind
  clear eq25
  have eq28 : (σ (k y y)) ≠ (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq26
    | exact resolve eq26 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq29 : (σ (k y y)) = (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq27
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq27
    | exact resolve eq27 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq33 : (k y y) = (τ (σ (k x x))) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq29
       grind)
    | exact superpose eq29 eq10
    | exact resolve eq10 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq36 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq33
       have i₂ := eq10 (k x x)
       grind)
    | exact superpose eq10 eq33
    | exact resolve eq33 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq39 : (σ (k x y)) ≠ (σ (k x y)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq36
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq36
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq36
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq36
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq36 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq41 : (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by grind
  clear eq39
  have eq43 : (k y y) = (M.op x x) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq41
  have eq45 : (k y y) = (k x x) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq43
  have eq46 : (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq45
  have eq47 : (σ (k x x)) ≠ (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq28
       have i₂ := eq46
       grind)
    | exact superpose eq46 eq28
    | exact resolve eq28 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq48 : (σ (k x x)) ≠ (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq47
  have eq49 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq48
  have eq51 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x x) ≠ (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq49
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq49
       have r₂ := eq13 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq49
       have r₂ := eq13 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq49 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq52 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x x) ≠ (M.op y y) := by grind
  clear eq51
  have eq53 : (σ x) = (σ y) ∨ x = y ∨ (M.op x x) ≠ (M.op y y) := by grind
  clear eq52
  have eq55 : (k y y) ≠ (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq53
  have eq57 : (k y y) ≠ (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq55
  have eq59 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq57
       have r₂ := eq46
       grind)
    | exact resolve eq57 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq57
  have eq63 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq59
       grind)
    | exact superpose eq59 eq10
    | exact resolve eq10 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq64 : x = y ∨ x = y := by
    first
    | (have i₁ := eq63
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq63
    | exact resolve eq63 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq65 : x = y := by grind
  clear eq64
  have eq70 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq65
       grind)
    | exact superpose eq65 eq16
    | exact resolve eq16 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq71 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq70
  have eq72 : (k (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq71
  have eq73 : False := by grind
  exact eq73

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_y_pyx_Equation1061 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1061 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = X1 := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
    intro X0 X1 X2
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X1) := by
    intro X0 X1
    grind
  have eq20 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq20
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq32 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq23
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq68 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 (σ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq32
    | exact resolve eq32 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq131 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq68 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq68
    | exact resolve eq68 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq154 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (k X0 X0)) X0)) = X1 := by
    intro X0 X1
    grind
  have eq156 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 (M.op X2 (M.op X0 X2))
       have i₂ := eq16 X0 X2 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq131 X1 (σ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq131
    | exact resolve eq131 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq131 (σ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq131
    | exact resolve eq131 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq470 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq226 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq226
    | exact resolve eq226 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq513 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq234 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq234
    | exact resolve eq234 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq801 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq470 (σ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq470
    | exact resolve eq470 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq856 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq513 (σ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq513
    | exact resolve eq513 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq1219 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ x = y ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq19 y x
       grind)
    | exact superpose eq19 eq9
    | (have j1 := eq19 x y
       grind)
    | (have r₁ := eq9
       have r₂ := eq19 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq9
       have r₂ := eq19 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1221 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (k X0 X1)) X1)) = X2 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq16
    | (have j1 := eq19 X0 X1
       grind)
    | exact resolve eq16 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1228 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq1219
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq1219
    | exact resolve eq1219 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219
  have eq1304 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1228
       have i₂ := eq19 (σ y) (σ x)
       grind)
    | exact superpose eq19 eq1228
    | (have j1 := eq19 x y
       grind)
    | (have r₁ := eq1228
       have r₂ := eq19 (σ y) (σ x)
       grind)
    | (have r₁ := eq1228
       have r₂ := eq19 (M.op (σ x) (σ y)) (k (σ y) (σ x))
       grind)
    | (have r₁ := eq1228
       have r₂ := eq19 (k (σ y) (σ x)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1228 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1228
  have eq1305 : x = y ∨ (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1304
  have eq1381 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1305
       grind)
    | exact superpose eq1305 eq9
    | exact resolve eq9 eq1305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1305
  have eq1382 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1381
  have eq1383 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1382
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1382
    | exact resolve eq1382 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1382
  have eq1384 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1383
  have eq1385 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1384
  have eq1467 : (k x x) ≠ (k x x) ∨ x = y ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq18 y x
       have i₂ := eq1385
       grind)
    | exact superpose eq1385 eq18
    | (have j0 := eq18 x y
       grind)
    | (have r₁ := eq18 y x
       have r₂ := eq1385
       grind)
    | (have r₁ := eq18 (σ y) (σ x)
       have r₂ := eq1385
       grind)
    | exact resolve eq18 eq1385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1385
  have eq1469 : x = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1467
  have eq1552 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq1469
       grind)
    | exact superpose eq1469 eq10
    | exact resolve eq10 eq1469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1469
  have eq1926 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq18 (σ y) (σ x)
       have i₂ := eq1552
       grind)
    | exact superpose eq1552 eq18
    | (have j0 := eq18 (σ x) (σ y)
       grind)
    | (have r₁ := eq18 (σ y) (σ x)
       have r₂ := eq1552
       grind)
    | exact resolve eq18 eq1552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1552
  have eq1928 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq1926
  have eq1929 : x = y ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq1928
  have eq1932 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1929
       grind)
    | exact superpose eq1929 eq9
    | exact resolve eq9 eq1929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1929
  have eq1933 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq1932
  have eq1934 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1933
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1933
    | exact resolve eq1933 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1933
  have eq1935 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq1934
  have eq1936 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq1935
  have eq1951 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq801 y (σ x)
       have i₂ := eq1936
       grind)
    | exact superpose eq1936 eq801
    | exact resolve eq801 eq1936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq1980 : x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1951
       have i₂ := eq15 x
       grind)
    | exact superpose eq15 eq1951
    | exact resolve eq1951 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1951
  have eq2765 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq856 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq856
    | exact resolve eq856 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq4862 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2765 (σ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2765
    | exact resolve eq2765 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2765
  have eq12608 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ x)) (σ x))) = X0 ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1221 (σ y) (σ x) X0
       have i₂ := eq1936
       grind)
    | exact superpose eq1936 eq1221
    | (have j0 := eq1221 (M.op X0 (M.op (M.op (σ y) (σ x)) (σ x))) X0 x
       grind)
    | exact resolve eq1221 eq1936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1936
  have eq12647 : ∀ X0 : G, (M.op x y) = (k x x) ∨ x = y ∨ (M.op X0 (M.op (M.op y x) x)) = X0 ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1221 y x X0
       have i₂ := eq1980
       grind)
    | exact superpose eq1980 eq1221
    | (have j0 := eq1221 (M.op x y) (k x x) x
       grind)
    | exact resolve eq1221 eq1980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221 eq1980
  have eq12718 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op X0 (M.op (M.op (σ y) (σ x)) (σ x))) = X0 := by
    intro X0
    first
    | (have j0 := eq12608 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12608
  have eq12815 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (σ (k x x)) ∨ x = y ∨ (M.op X0 (M.op (M.op y x) x)) = X0 ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq9
       have i₂ := eq12647 X0
       grind)
    | exact superpose eq12647 eq9
    | (have j1 := eq12647 X0
       grind)
    | exact resolve eq9 eq12647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12647
  have eq12824 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ x = y ∨ (M.op X0 (M.op (M.op y x) x)) = X0 ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq12815 X0
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq12815
    | (have j0 := eq12815 X0
       grind)
    | exact resolve eq12815 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12815
  have eq13791 : ∀ X0 X1 : G, (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ x = y ∨ (M.op X0 (M.op (M.op y x) x)) = X0 ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op X1 (M.op (M.op (σ y) (σ x)) (σ x))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12824 X0
       have i₂ := eq12718 X1
       grind)
    | exact superpose eq12718 eq12824
    | (have j0 := eq12824 X0
       have j1 := eq12718 X1
       grind)
    | (have r₁ := eq12824 X0
       have r₂ := eq12718 X0
       grind)
    | exact resolve eq12824 eq12718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12718 eq12824
  have eq13809 : ∀ X0 X1 : G, (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ x = y ∨ (M.op X0 (M.op (M.op y x) x)) = X0 ∨ (σ x) = (σ y) ∨ (M.op X1 (M.op (M.op (σ y) (σ x)) (σ x))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13791 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13791
  have eq13810 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ y) (σ x)) (σ x))) = X1 ∨ (M.op X0 (M.op (M.op y x) x)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq13809 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13809
  have eq17973 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (M.op X1 (M.op (M.op y x) x)) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (σ x) (M.op (σ y) (σ x))
       have i₂ := eq13810 X1 (σ x)
       grind)
    | exact superpose eq13810 eq16
    | (have j1 := eq13810 X1 X1
       grind)
    | exact resolve eq16 eq13810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13810
  have eq18238 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op y x) x)) = X1 ∨ (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq156 (σ y) X0 (σ x)
       have i₂ := eq17973 (σ y) X1
       grind)
    | exact superpose eq17973 eq156
    | (have j1 := eq17973 X0 X1
       grind)
    | exact resolve eq156 eq17973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17973
  have eq18593 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op y x))) = X0 ∨ (M.op X1 (σ y)) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x (M.op y x)
       have i₂ := eq18238 X1 x
       grind)
    | exact superpose eq18238 eq16
    | (have j1 := eq18238 X1 X1
       grind)
    | exact resolve eq16 eq18238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18238
  have eq18955 : ∀ X0 X1 : G, (M.op X0 y) = X0 ∨ (M.op X1 (σ y)) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq156 y X0 x
       have i₂ := eq18593 y X1
       grind)
    | exact superpose eq18593 eq156
    | (have j1 := eq18593 X0 X1
       grind)
    | exact resolve eq156 eq18593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156 eq18593
  have eq19009 : ∀ X0 : G, y = (k y y) ∨ (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    grind
  clear eq18955
  have eq19057 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10 y y
       have i₂ := eq19009 X0
       grind)
    | exact superpose eq19009 eq10
    | (have j1 := eq19009 X0
       grind)
    | exact resolve eq10 eq19009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19009
  have eq19628 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq19057
  have eq19686 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq19628
  have eq19765 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4862 y (σ y)
       have i₂ := eq19686
       grind)
    | exact superpose eq19686 eq4862
    | exact resolve eq4862 eq19686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4862
  have eq19771 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ y)) (σ y))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq154 (σ y) X0
       have i₂ := eq19686
       grind)
    | exact superpose eq19686 eq154
    | exact resolve eq154 eq19686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19776 : ∀ X0 : G, (M.op X0 (M.op (k (σ y) (σ y)) (σ y))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    grind
  clear eq19771
  have eq19777 : y = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq19765
       have i₂ := eq15 y
       grind)
    | exact superpose eq15 eq19765
    | exact resolve eq19765 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19765
  have eq19840 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq19686 eq19776
    | exact resolve eq19776 eq19686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19776
  have eq19841 : ∀ X0 : G, (M.op X0 (k (σ y) (σ y))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    grind
  clear eq19840
  have eq19842 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq19686 eq19841
    | exact resolve eq19841 eq19686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19686 eq19841
  have eq19850 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq154 y X0
       have i₂ := eq19777
       grind)
    | exact superpose eq19777 eq154
    | exact resolve eq154 eq19777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq19857 : ∀ X0 : G, (M.op X0 (M.op (k y y) y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    grind
  clear eq19850
  have eq19860 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq19777 eq19857
    | exact resolve eq19857 eq19777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19857
  have eq19863 : ∀ X0 : G, (M.op X0 (k y y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    grind
  clear eq19860
  have eq19864 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq19777 eq19863
    | exact resolve eq19863 eq19777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19777 eq19863
  have eq19896 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9
       have i₂ := eq19864 x
       grind)
    | exact superpose eq19864 eq9
    | exact resolve eq9 eq19864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19864
  have eq19907 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq19896
       have r₂ := eq19842 (σ x)
       grind)
    | exact resolve eq19896 eq19842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19842 eq19896
  have eq19921 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq19907
       grind)
    | exact superpose eq19907 eq9
    | exact resolve eq9 eq19907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19907
  have eq19922 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq19921
  have eq19923 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19922
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq19922
    | exact resolve eq19922 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19922
  have eq19924 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq19923
  have eq19925 : (σ x) = (σ y) := by grind
  clear eq19924
  have eq19927 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq19925
       grind)
    | exact superpose eq19925 eq15
    | exact resolve eq15 eq19925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19925
  have eq20056 : x = y := by
    first
    | (have i₁ := eq19927
       have i₂ := eq15 x
       grind)
    | exact superpose eq15 eq19927
    | exact resolve eq19927 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19927
  have eq20059 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq20056
       grind)
    | exact superpose eq20056 eq9
    | exact resolve eq9 eq20056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20056
  have eq20060 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq20059
  have eq20061 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq20060
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq20060
    | exact resolve eq20060 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20060
  have eq20062 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) := by grind
  clear eq20061
  have eq20063 : False := by grind
  exact eq20063

/-- `Equation1063`: `x = x ◇ ((y ◇ (z ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxx_pxy_pxy_pxx_pxy_Equation1063 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1063 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1063.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X2)) X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq29 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
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
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq33 (σ X0)
       grind)
    | exact superpose eq33 eq15
    | exact resolve eq15 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq33 (τ X0)
       grind)
    | exact superpose eq33 eq18
    | exact resolve eq18 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq37
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq40 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq35
    | exact resolve eq35 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq42 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq38
    | exact resolve eq38 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq44 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq76 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq40 (k X1 (τ X0))
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq40
    | exact resolve eq40 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq90 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq103 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq10
    | exact resolve eq10 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq149 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 (τ (M.op X0 X0))) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 (τ X0)
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq9
    | exact resolve eq9 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq93 (k X1 (τ X0)) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq93
    | exact resolve eq93 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq93
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq199 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq171 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq171
    | (have j0 := eq171 X0 X1
       grind)
    | exact resolve eq171 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq201 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq169 X0 X1 X2
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq169
    | (have j0 := eq169 X0 X1 X2
       grind)
    | exact resolve eq169 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq206 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq199 X0 X1
       have j1 := eq78 X1 X0
       grind)
    | (have r₁ := eq199 (σ X0) X0
       have r₂ := eq78 X0 (σ X0)
       grind)
    | (have r₁ := eq199 X1 X0
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq199 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq199
  have eq208 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq201 X0 X1 X2
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq201
    | (have j0 := eq201 X0 X1 X2
       grind)
    | exact resolve eq201 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq201
  have eq219 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 (τ (τ (M.op X0 X0)))) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq149 (τ X0) X1 X2
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq149
    | exact resolve eq149 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq149
  have eq624 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq206 X1 X0
       grind)
    | exact superpose eq206 eq30
    | (have j1 := eq206 X1 X0
       grind)
    | exact resolve eq30 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq2028 : ∀ X0 X1 X2 X3 : G, (M.op (k (σ X0) X1) (σ X2)) ≠ (M.op (k (σ X0) X1) X3) ∨ (M.op (k (σ X0) X1) (σ X2)) = (k (k (σ X0) X1) X3) ∨ (M.op (k (σ X0) X1) (σ X2)) = (M.op X3 (k (σ X0) X1)) ∨ (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (k (σ X0) X1) X1
       have i₂ := eq208 X0 X1 X2
       grind)
    | exact superpose eq208 eq13
    | (have j0 := eq13 (k (σ X0) X1) (σ X2)
       have j1 := eq208 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (σ X2)
       have r₂ := eq208 X0 X1 X2
       grind)
    | exact resolve eq13 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2068 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (σ X2)) ≠ (M.op (σ X2) (k (σ X0) X1)) ∨ (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq208 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq2465 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op X1 (M.op X2 X2)) (σ X0)))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq624 X0 (M.op (M.op X1 (M.op X2 X2)) (σ X0))
       have i₂ := eq9 (σ X0) X1 X2
       grind)
    | exact superpose eq9 eq624
    | exact resolve eq624 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq2535 : ∀ X0 X1 X2 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (τ (M.op (M.op X1 (M.op X2 X2)) (σ X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2465 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2465
    | (have j0 := eq2465 X0 X1 X2
       grind)
    | exact resolve eq2465 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2465
  have eq9402 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k X0 (τ (M.op (M.op X1 (M.op X2 X2)) (σ X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq2535 X0 X1 X2
       grind)
    | exact superpose eq2535 eq10
    | (have j1 := eq2535 X0 X1 X2
       grind)
    | exact resolve eq10 eq2535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2535
  have eq9468 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op (M.op X1 (M.op X2 X2)) (σ X0)))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9402 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9402
    | (have j0 := eq9402 X0 X1 X2
       grind)
    | exact resolve eq9402 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9402
  have eq9704 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op (M.op X1 (M.op X2 X2)) (σ (σ X0)))))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 (τ (M.op (M.op X1 (M.op X2 X2)) (σ (σ X0))))
       have i₂ := eq9468 (σ X0) X1 X2
       grind)
    | exact superpose eq9468 eq30
    | (have j1 := eq9468 (σ X0) X1 X2
       grind)
    | exact resolve eq30 eq9468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq9468
  have eq9794 : ∀ X0 X1 X2 : G, (k X0 (τ (τ (M.op (M.op X1 (M.op X2 X2)) (σ (σ X0)))))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9704 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9704
    | (have j0 := eq9704 X0 X1 X2
       grind)
    | exact resolve eq9704 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9704
  have eq9841 : ∀ X0 X1 X2 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (τ (τ (M.op (M.op X1 (M.op X2 X2)) (σ (σ X0)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9794 X0 X1 X2
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq9794
    | (have j0 := eq9794 X0 X1 X2
       grind)
    | exact resolve eq9794 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq9794
  have eq62712 : ∀ X0 X1 X2 : G, (M.op (σ X2) (k X0 X1)) ≠ (M.op (k X0 X1) (σ X2)) ∨ (M.op (σ X2) (k X0 X1)) = (M.op (k X0 X1) (k X0 X1)) ∨ (σ (k (k (τ X0) (τ X1)) X2)) = (M.op (k X0 X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2068 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2068
    | exact resolve eq2068 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2068
  have eq62963 : ∀ X0 X1 X2 : G, (σ (k (τ (k X0 X1)) X2)) = (M.op (k X0 X1) (σ X2)) ∨ (M.op (σ X2) (k X0 X1)) ≠ (M.op (k X0 X1) (σ X2)) ∨ (M.op (σ X2) (k X0 X1)) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62712 X0 X1 X2
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq62712
    | (have j0 := eq62712 X0 X1 X2
       grind)
    | exact resolve eq62712 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq62712
  have eq63059 : ∀ X0 X1 X2 : G, (k (k X0 X1) (σ X2)) = (M.op (k X0 X1) (σ X2)) ∨ (M.op (σ X2) (k X0 X1)) ≠ (M.op (k X0 X1) (σ X2)) ∨ (M.op (σ X2) (k X0 X1)) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62963 X0 X1 X2
       have i₂ := eq17 (k X0 X1) X2
       grind)
    | exact superpose eq17 eq62963
    | (have j0 := eq62963 X0 X1 X2
       grind)
    | exact resolve eq62963 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq62963
  have eq63101 : ∀ X0 X1 X2 : G, (k (k X0 X1) (σ X2)) = (M.op (k X0 X1) (σ X2)) ∨ (M.op (σ X2) (k X0 X1)) ≠ (M.op (k X0 X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq63059 X0 X1 X2
       have j1 := eq12 (k X0 X1) (σ X2)
       grind)
    | (have r₁ := eq63059 X0 X1 X2
       have r₂ := eq12 (k X0 X1) (σ X2)
       grind)
    | exact resolve eq63059 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63059
  have eq67264 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k X0 (τ (τ (M.op (M.op X1 (M.op X2 X2)) (σ (σ X0)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq9841 X0 X1 X2
       grind)
    | exact superpose eq9841 eq10
    | (have j1 := eq9841 X0 X1 X2
       grind)
    | exact resolve eq10 eq9841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9841
  have eq67406 : ∀ X0 X1 X2 : G, (k X0 (τ (τ (M.op (M.op X1 (M.op X2 X2)) (σ (σ X0)))))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67264 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq67264
    | (have j0 := eq67264 X0 X1 X2
       grind)
    | exact resolve eq67264 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67264
  have eq67449 : ∀ X0 X1 X2 : G, (k X2 (τ (τ (M.op (M.op X0 (τ (τ (M.op X1 X1)))) (σ (σ X2)))))) = X2 ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67406 X2 (M.op X0 (τ (τ (M.op X1 X1)))) (M.op X0 (τ (τ (M.op X1 X1))))
       have i₂ := eq219 X1 (M.op X0 (τ (τ (M.op X1 X1)))) X0
       grind)
    | exact superpose eq219 eq67406
    | (have j0 := eq67406 X2 X1 X2
       grind)
    | exact resolve eq67406 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq67406
  have eq178868 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (M.op (k (σ X0) X1) (σ X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2028 X0 X1 X2 (σ X2)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2028
  have eq178871 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (M.op (k (σ X0) X1) (σ X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq178868 X0 X1 X2
       have j1 := eq12 (k (σ X0) X1) (σ X2)
       grind)
    | (have r₁ := eq178868 X0 X1 X2
       have r₂ := eq12 (k (σ X0) X1) (σ X2)
       grind)
    | exact resolve eq178868 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178868
  have eq179047 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq178871 X0 X1 X2
       have j1 := eq63101 (σ X0) X1 X2
       grind)
    | (have r₁ := eq178871 X0 X1 X2
       have r₂ := eq63101 (σ X0) X1 X2
       grind)
    | exact resolve eq178871 eq63101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63101 eq178871
  have eq179191 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179047 X0 X1 X2
       have i₂ := eq29 X0 X1 X2
       grind)
    | exact superpose eq29 eq179047
    | (have j0 := eq179047 X0 X1 X2
       grind)
    | exact resolve eq179047 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq179047
  have eq179192 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq179191 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179191
  have eq179692 : ∀ X0 X1 X2 : G, (k (σ (k X0 (τ X1))) X2) = (M.op (k (σ X0) X1) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X2 (k X0 (τ X1))
       have i₂ := eq179192 X0 X1 (τ X2)
       grind)
    | exact superpose eq179192 eq18
    | exact resolve eq18 eq179192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179192
  have eq180040 : ∀ X0 X1 X2 : G, (k (σ (k X0 (τ X1))) X2) = (M.op (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179692 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq179692
    | exact resolve eq179692 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179692
  have eq180362 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) X2) = (M.op (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180040 X0 X1 X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq180040
    | exact resolve eq180040 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq180040
  have eq180594 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (M.op (k X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180362 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq180362
    | exact resolve eq180362 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180362
  have eq184252 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq180594 X0 X0 x
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq180594
    | exact resolve eq180594 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq184363 : ∀ X0 X3 : G, (M.op X0 X0) = X0 ∨ (k X0 X3) = (M.op X0 X3) := by
    intro X0 X3
    first
    | (have i₁ := eq180594 x (τ (τ (M.op (M.op X0 (τ (τ (M.op x x)))) (σ (σ x))))) x
       have i₂ := eq67449 X0 x x
       grind)
    | exact superpose eq67449 eq180594
    | (have j1 := eq67449 X0 x X0
       grind)
    | exact resolve eq180594 eq67449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67449 eq180594
  have eq188868 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq184252 X0 X1
       have i₂ := eq184363 X0 x
       grind)
    | exact superpose eq184363 eq184252
    | (have j1 := eq184363 X0 X1
       grind)
    | exact resolve eq184252 eq184363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184252 eq184363
  have eq259564 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq188868 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188868
  have eq259565 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq259564 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259564
  have eq261736 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq259565 (σ X0) (σ X1)
       grind)
    | exact superpose eq259565 eq15
    | exact resolve eq15 eq259565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262021 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq261736 X0 X1
       have i₂ := eq259565 X0 X1
       grind)
    | exact superpose eq259565 eq261736
    | exact resolve eq261736 eq259565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259565 eq261736
  have eq300247 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq262021 x y
       grind)
    | exact superpose eq262021 eq16
    | (have r₁ := eq16
       have r₂ := eq262021 x y
       grind)
    | exact resolve eq16 eq262021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262021
  have eq300683 : False := by grind
  exact eq300683
