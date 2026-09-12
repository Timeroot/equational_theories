import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3461`: `x ◇ x = x ◇ ((y ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pxy_pxx_pxy_Equation3461 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3461 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3461.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X1 X0) X0)) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq452 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X1 (M.op X0 X1)) ∨ (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 (M.op X0 X1) X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq460 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X1)) ∨ (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have j0 := eq452 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq471 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have j0 := eq460 X0 X1
       have j1 := eq12 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq460 X0 X1
       have r₂ := eq12 (M.op X0 X1) X1
       grind)
    | exact resolve eq460 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq492 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq471 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq471
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq471 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq505 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq492 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq510 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq505 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq505 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq505 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq505 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq531 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq510 (σ X0) (σ X1)
       grind)
    | exact superpose eq510 eq15
    | exact resolve eq15 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq558 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq531 X0 X1
       have i₂ := eq510 X0 X1
       grind)
    | exact superpose eq510 eq531
    | exact resolve eq531 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510 eq531
  have eq796 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq558 x y
       grind)
    | exact superpose eq558 eq16
    | (have r₁ := eq16
       have r₂ := eq558 x y
       grind)
    | exact resolve eq16 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq811 : False := by grind
  exact eq811

/-- `Equation3461`: `x ◇ x = x ◇ ((y ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation3461 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3461 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3461.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq265 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq265 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq268 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq266 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq266 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq266 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq279 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq268 (σ X0)
       grind)
    | exact superpose eq268 eq15
    | exact resolve eq15 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq279 X0
       have i₂ := eq268 X0
       grind)
    | exact superpose eq268 eq279
    | exact resolve eq279 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq279
  have eq343 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq345 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq343 X0 X1
       have j1 := eq344 X0 X1
       grind)
    | (have r₁ := eq343 X0 X1
       have r₂ := eq344 X0 X1
       grind)
    | exact resolve eq343 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq344
  have eq404 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq345 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq345
    | exact resolve eq345 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq414 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq345 y (σ x)
       grind)
    | exact superpose eq345 eq16
    | (have j1 := eq345 y (σ x)
       grind)
    | exact resolve eq16 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq420 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq414
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq414
    | exact resolve eq414 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq433 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq404 X0 X1
       grind)
    | exact superpose eq404 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq404 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq404 X0 X1
       grind)
    | exact resolve eq13 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq433 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq450 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq443 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq443 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq443 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq475 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq450 X1 (τ X0)
       grind)
    | exact superpose eq450 eq17
    | (have j1 := eq450 X1 (τ X0)
       grind)
    | exact resolve eq17 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq481 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq450 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq475 X1 (τ X0)
       grind)
    | exact superpose eq475 eq18
    | (have j1 := eq475 X1 (τ X0)
       grind)
    | exact resolve eq18 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq475
  have eq681 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq674 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq674
    | (have j0 := eq674 X0 X1
       grind)
    | exact resolve eq674 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq696 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq681 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq681
    | (have j0 := eq681 X0 X1
       grind)
    | exact resolve eq681 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq699 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq696 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq696
    | (have j0 := eq696 X0 X1
       grind)
    | exact resolve eq696 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq756 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq699 X0 X1
       have i₂ := eq450 X0 X1
       grind)
    | exact superpose eq450 eq699
    | (have j0 := eq699 X1 X0
       have j1 := eq450 X1 X0
       grind)
    | exact resolve eq699 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450 eq699
  have eq819 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq756 X0 X1
       have j1 := eq481 X0 X1
       grind)
    | (have r₁ := eq756 X0 X1
       have r₂ := eq481 X0 X1
       grind)
    | exact resolve eq756 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481 eq756
  have eq860 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq819 X1 (σ X0)
       grind)
    | exact superpose eq819 eq22
    | (have j1 := eq819 X1 (σ X0)
       grind)
    | exact resolve eq22 eq819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq819
  have eq896 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq860 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq860
    | (have j0 := eq860 X0 X1
       grind)
    | exact resolve eq860 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860
  have eq915 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq896 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq896
    | (have j0 := eq896 X0 X1
       grind)
    | exact resolve eq896 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq1194 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq915 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq915
    | exact resolve eq915 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915
  have eq1262 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1194 x y
       grind)
    | exact superpose eq1194 eq16
    | (have j1 := eq1194 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1194 x y
       grind)
    | exact resolve eq16 eq1194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194
  have eq1280 : y = (k x y) := by grind
  clear eq1262
  have eq1395 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq420
       have i₂ := eq404 y x
       grind)
    | exact superpose eq404 eq420
    | (have j1 := eq404 y x
       grind)
    | exact resolve eq420 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1396 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq1395
  have eq1397 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1396
       have i₂ := eq1280
       grind)
    | exact superpose eq1280 eq1396
    | exact resolve eq1396 eq1280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396
  have eq1398 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1397
       have i₂ := eq1280
       grind)
    | exact superpose eq1280 eq1397
    | exact resolve eq1397 eq1280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397
  have eq1399 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq420
       have i₂ := eq1398
       grind)
    | exact superpose eq1398 eq420
    | exact resolve eq420 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420 eq1398
  have eq1407 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1399
  have eq1408 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1407
       have i₂ := eq1280
       grind)
    | exact superpose eq1280 eq1407
    | exact resolve eq1407 eq1280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407
  have eq1409 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1408
  have eq1411 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1409
       grind)
    | exact superpose eq1409 eq16
    | exact resolve eq16 eq1409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409
  have eq1428 : (σ y) ≠ (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1411
       have i₂ := eq404 y x
       grind)
    | exact superpose eq404 eq1411
    | (have j1 := eq404 y x
       grind)
    | exact resolve eq1411 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq1429 : (M.op x y) = (k x y) := by grind
  clear eq1428
  have eq1431 : y = (M.op x y) := by
    first
    | (have i₁ := eq1429
       have i₂ := eq1280
       grind)
    | exact superpose eq1280 eq1429
    | exact resolve eq1429 eq1280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280 eq1429
  have eq1432 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1411
       have i₂ := eq1431
       grind)
    | exact superpose eq1431 eq1411
    | exact resolve eq1411 eq1431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411 eq1431
  have eq1442 : False := by grind
  exact eq1442

/-- `Equation3477`: `x ◇ x = y ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxy_pxx_pxy_Equation3477 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3477 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3477.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X2) X0)) := by
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
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
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X0) X2 x
       have i₂ := eq14 X0 (M.op (M.op (M.op X0 X1) X0) x) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq56 X0 x X2
       have i₂ := eq14 X0 (M.op (M.op X0 x) X0) x
       grind)
    | (have i₁ := eq56 X0 x X2
       have i₂ := eq14 (M.op (M.op X0 x) X0) x X2
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 (M.op y y) y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq73
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq73
    | exact resolve eq73 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq76
    | exact resolve eq76 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq90 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq94 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq90
  have eq95 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq94
  have eq126 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq95
       grind)
    | exact superpose eq95 eq16
    | exact resolve eq16 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq405 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (σ X0) x
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq57
    | exact resolve eq57 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq9754 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq77 eq11
    | (have j0 := eq11 (M.op (σ y) (σ y)) (σ y)
       grind)
    | exact resolve eq11 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq9755 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq9754
    | exact resolve eq9754 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9754
  have eq9766 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq9755
       have r₂ := eq28
       grind)
    | exact resolve eq9755 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9755
  have eq9770 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq9766 eq126
    | exact resolve eq126 eq9766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq9766
  have eq9810 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq30 eq9770
    | exact resolve eq9770 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9770
  have eq9811 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq9810
  have eq9823 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq57 y x
       have i₂ := eq9811
       grind)
    | exact superpose eq9811 eq57
    | exact resolve eq57 eq9811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq9825 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq405 y x
       have i₂ := eq9811
       grind)
    | exact superpose eq9811 eq405
    | exact resolve eq405 eq9811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405 eq9811
  have eq9847 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9825 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq9825
    | (have j0 := eq9825 X0
       grind)
    | exact resolve eq9825 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9825
  have eq10137 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq9823 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9823
    | (have j0 := eq9823 x
       grind)
    | exact resolve eq9823 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9823
  have eq10200 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq10137 eq30
    | exact resolve eq30 eq10137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10137
  have eq10300 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq10200
    | exact resolve eq10200 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10200
  have eq10301 : y = (M.op x y) ∨ x = y := by grind
  clear eq10300
  have eq10318 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq10301 eq21
    | exact resolve eq21 eq10301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10301
  have eq10421 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10318
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10318
    | exact resolve eq10318 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10318
  have eq13332 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq9847
    | (have j0 := eq9847 (σ x)
       grind)
    | exact resolve eq9847 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9847
  have eq13532 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13332 eq28
    | exact resolve eq28 eq13332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13332
  have eq13533 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq13532
       have r₂ := eq10421
       grind)
    | exact resolve eq13532 eq10421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10421 eq13532
  have eq13536 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq13533 eq30
    | exact resolve eq30 eq13533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq13533
  have eq13663 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq13536
    | exact resolve eq13536 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq13536
  have eq13664 : x = y := by grind
  clear eq13663
  have eq13683 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq13664
       grind)
    | exact superpose eq13664 eq19
    | exact resolve eq19 eq13664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq13684 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq13664
       grind)
    | exact superpose eq13664 eq25
    | exact resolve eq25 eq13664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq13664
  have eq13785 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq13684
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq13684
    | exact resolve eq13684 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq13684
  have eq13802 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq13785 eq27
    | exact resolve eq27 eq13785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq13785
  have eq14012 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq13802 eq69
    | exact resolve eq69 eq13802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq13802
  have eq14049 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq14012
       have i₂ := eq13683
       grind)
    | exact superpose eq13683 eq14012
    | exact resolve eq14012 eq13683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13683 eq14012
  have eq14060 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14049 eq15
    | exact resolve eq15 eq14049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14049
  have eq14106 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq14060
    | exact resolve eq14060 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq14060
  have eq14115 : False := by grind
  exact eq14115

/-- `Equation3487`: `x ◇ x = y ◇ ((y ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pyx_Equation3487 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3487 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3487.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ y) (σ x)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ y) (σ x)
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
  have eq19 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13 (σ x) (σ y)
       grind)
    | exact superpose eq13 eq16
    | (have j1 := eq13 (σ y) (σ x)
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
  have eq20 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq19
    | exact resolve eq19 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq21 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq18
    | exact resolve eq18 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq22 : (M.op (σ y) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by grind
  clear eq20
  have eq23 : (M.op (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by grind
  clear eq21
  have eq24 : (M.op (σ y) (σ y)) ≠ (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq22
    | exact resolve eq22 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq25 : (M.op (σ y) (σ y)) = (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq23
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq23
    | exact resolve eq23 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq26 : (σ (k x x)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by grind
  clear eq24
  have eq27 : (σ (k x x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by grind
  clear eq25
  have eq28 : (σ (k x x)) ≠ (σ (k y y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq26
    | exact resolve eq26 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq29 : (σ (k x x)) = (σ (k y y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq27
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq27
    | exact resolve eq27 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq33 : (k y y) = (τ (σ (k x x))) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
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
  have eq36 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) := by
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
  have eq39 : (σ (k y x)) ≠ (σ (k y x)) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq36
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq36
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq36
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq36
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq36 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq41 : (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op x x) ∨ x = y := by grind
  clear eq39
  have eq43 : (k x x) = (M.op y y) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq41
  have eq45 : (k x x) = (k y y) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq43
  have eq46 : (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq45
  have eq47 : (σ (k x x)) ≠ (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
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
  have eq48 : (σ (k x x)) ≠ (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq47
  have eq49 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq48
  have eq51 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op y y) ≠ (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq49
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq49
       have r₂ := eq13 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq49
       have r₂ := eq13 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq49 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq52 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op y y) ≠ (M.op x x) := by grind
  clear eq51
  have eq53 : (σ x) = (σ y) ∨ x = y ∨ (M.op y y) ≠ (M.op x x) := by grind
  clear eq52
  have eq55 : (k x x) ≠ (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq53
  have eq57 : (k x x) ≠ (k y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
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

/-- `Equation3491`: `x ◇ x = y ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_y_pxy_pxx_pxy_Equation3491 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3491 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3491.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X0) X0)) := by
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
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X0) (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X1 X0) X0) X2 x
       have i₂ := eq14 X0 (M.op x (M.op (M.op X1 X0) X0)) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq53 X0 x X2
       have i₂ := eq14 X0 (M.op (M.op x X0) X0) x
       grind)
    | (have i₁ := eq53 X0 x X2
       have i₂ := eq14 (M.op (M.op x X0) X0) x X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq70 x y
       grind)
    | exact superpose eq70 eq44
    | (have j1 := eq70 x y
       grind)
    | exact resolve eq44 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq92
    | exact resolve eq92 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq98
    | exact resolve eq98 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq105 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq99 eq70
    | (have j0 := eq70 x (σ y)
       grind)
    | exact resolve eq70 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq653 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq652
    | exact resolve eq652 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq656 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq653
       have r₂ := eq27
       grind)
    | exact resolve eq653 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq659 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq656 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq656
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq656
       grind)
    | exact resolve eq13 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq656 eq54
    | exact resolve eq54 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq665 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq659
  have eq703 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq662
    | (have j0 := eq662 (σ x)
       grind)
    | exact resolve eq662 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq726 : y ≠ y ∨ y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq703
       grind)
    | exact superpose eq703 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq703
       grind)
    | exact resolve eq13 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq728 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq726
  have eq789 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq728
       grind)
    | exact superpose eq728 eq77
    | exact resolve eq77 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq728
  have eq793 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq789
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq789
    | exact resolve eq789 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq834 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq793 eq70
    | (have j0 := eq70 x (σ y)
       grind)
    | exact resolve eq70 eq793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793
  have eq835 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq834
  have eq840 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq835 eq54
    | exact resolve eq54 eq835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq864 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq840 eq26
    | (have j1 := eq840 (σ x)
       grind)
    | exact resolve eq26 eq840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq840
  have eq866 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq864
  have eq873 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq866 eq27
    | exact resolve eq27 eq866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq866
  have eq911 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq665 eq105
    | exact resolve eq105 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq665
  have eq915 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq911
    | exact resolve eq911 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq911
  have eq918 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq70 y y
       have i₂ := eq915
       grind)
    | exact superpose eq915 eq70
    | (have j0 := eq70 x y
       grind)
    | exact resolve eq70 eq915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq915
  have eq919 : y = (M.op y y) := by grind
  clear eq918
  have eq924 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq54 y x
       have i₂ := eq919
       grind)
    | exact superpose eq919 eq54
    | exact resolve eq54 eq919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq919
  have eq936 : y = (M.op x y) := by
    first
    | (have i₁ := eq924 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq924
    | (have j0 := eq924 x
       grind)
    | exact resolve eq924 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq924
  have eq966 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq936 eq20
    | exact resolve eq20 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq936
  have eq985 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq966
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq966
    | exact resolve eq966 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq966
  have eq986 : False := by grind
  exact eq986

/-- `Equation3506`: `x ◇ x = y ◇ ((z ◇ w) ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_x_pxy_pyy_pxy_Equation3506 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3506 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3506.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X3) X3)) := by
    intro X0 X1 X2 X3
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq25 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x x x
       have i₂ := eq9 X1 x x x
       grind)
    | (have i₁ := eq9 X0 (M.op (M.op x x) x) x x
       have i₂ := eq9 (M.op (M.op x x) x) X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X2)) ≠ (M.op X0 (M.op (M.op X1 X2) X2)) ∨ (M.op X0 (M.op (M.op X1 X2) X2)) = (k X3 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq9 X0 X1 X2 X3
       grind)
    | (have i₁ := eq12 (M.op (M.op X2 X3) X3) X1
       have i₂ := eq9 X0 X1 X2 X3
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 (M.op (M.op X2 X3) X3) (M.op (M.op X2 X3) X3)
       have r₂ := eq9 (M.op (M.op X2 X3) X3) (M.op (M.op X2 X3) X3) X2 X3
       grind)
    | (have r₁ := eq12 (M.op (M.op X2 X3) X3) X0
       have r₂ := eq9 X0 X0 X2 X3
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X2) X2)) ≠ (M.op X3 X4) ∨ (k X4 X3) = (M.op X4 X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq12 X4 X3
       have i₂ := eq9 X3 X0 X1 X2
       grind)
    | (have i₁ := eq12 X0 (M.op (M.op X2 X3) X3)
       have i₂ := eq9 X0 (M.op (M.op X2 X3) X3) X2 X3
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X4 X3
       grind)
    | (have r₁ := eq12 (M.op (M.op X2 X3) X3) (M.op (M.op X2 X3) X3)
       have r₂ := eq9 (M.op (M.op X2 X3) X3) (M.op (M.op X2 X3) X3) X2 X3
       grind)
    | (have r₁ := eq12 (M.op (M.op X2 X3) X3) X0
       have r₂ := eq9 X0 X0 X2 X3
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X2)) = (k X3 X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq27 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq37 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X2) X2)) = (M.op X3 X4) ∨ (k X4 X3) = (M.op X4 X3) ∨ (M.op X0 (M.op (M.op X1 X2) X2)) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X0 X0
       have i₂ := eq9 X0 X1 X2 X3
       grind)
    | (have i₁ := eq14 X0 (M.op (M.op X2 X3) X3)
       have i₂ := eq9 X0 (M.op (M.op X2 X3) X3) X2 X3
       grind)
    | exact superpose eq9 eq14
    | (have j0 := eq14 X4 X3
       grind)
    | exact resolve eq14 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 X4 : G, (k X4 X3) = (M.op X4 X3) ∨ (M.op X0 (M.op (M.op X1 X2) X2)) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq37 X0 X1 X2 X3 X4
       have j1 := eq29 X0 X1 X2 X3 X4
       grind)
    | (have r₁ := eq37 X0 X1 X2 X3 X4
       have r₂ := eq29 X0 X1 X2 X3 X4
       grind)
    | (have r₁ := eq37 X3 X1 X2 X0 (M.op (M.op X1 X2) X2)
       have r₂ := eq29 X0 X1 X2 X3 (M.op (M.op X1 X2) X2)
       grind)
    | (have r₁ := eq37 X0 X1 X2 X3 (M.op X3 X4)
       have r₂ := eq29 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq37 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq37
  have eq77 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq25 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq25 X1 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq25 X0 X0
       grind)
    | exact resolve eq12 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq80 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq77 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq503 : ∀ X0 X1 X5 X6 : G, (M.op X1 X0) = (k X5 X5) ∨ (k X0 X6) = (M.op X0 X6) := by
    intro X0 X1 X5 X6
    first
    | (have i₁ := eq32 X1 x (M.op (M.op x x) x) X5
       have i₂ := eq56 (M.op x (M.op (M.op x x) x)) x x X6 X0
       grind)
    | (have i₁ := eq32 X0 X1 x x
       have i₂ := eq56 X0 X1 x x (M.op (M.op X1 x) x)
       grind)
    | exact superpose eq56 eq32
    | (have j1 := eq56 X0 X1 x X6 X0
       grind)
    | exact resolve eq32 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq56
  have eq545 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (k X0 X0) ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq80 X1 X0
       grind)
    | exact superpose eq80 eq12
    | (have j0 := eq12 X2 X1
       grind)
    | exact resolve eq12 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq581 : ∀ X1 X2 : G, (k X2 X1) = (M.op X2 X1) := by
    intro X1 X2
    first
    | (have j0 := eq545 x X1 X2
       have j1 := eq503 X2 X1 x X1
       grind)
    | (have r₁ := eq545 x X1 x
       have r₂ := eq503 x X1 x x
       grind)
    | (have r₁ := eq545 x x x
       have r₂ := eq503 x X1 x x
       grind)
    | exact resolve eq545 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503 eq545
  have eq2793 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq581 (σ X1) (σ X0)
       grind)
    | exact superpose eq581 eq15
    | exact resolve eq15 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2798 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2793 X0 X1
       have i₂ := eq581 X1 X0
       grind)
    | exact superpose eq581 eq2793
    | exact resolve eq2793 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581 eq2793
  have eq2802 : False := by grind
  exact eq2802

/-- `Equation3506`: `x ◇ x = y ◇ ((z ◇ w) ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxy_pxx_pxy_Equation3506 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3506 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3506.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X3) X3)) := by
    intro X0 X1 X2 X3
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
  have eq56 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 X3) = (M.op X4 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 X3 X4 X5 X5
       have i₂ := eq14 X5 X0 X1 X2
       grind)
    | (have i₁ := eq14 X0 X1 X1 (M.op (M.op X2 X3) X3)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x x x
       have i₂ := eq14 X1 x x x
       grind)
    | (have i₁ := eq14 X0 (M.op (M.op x x) x) x x
       have i₂ := eq14 (M.op (M.op x x) x) X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
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
  have eq124 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq119
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq119
    | exact resolve eq119 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq125 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq124
    | exact resolve eq124 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq608 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 X1) = (M.op X2 (M.op (M.op X3 (M.op (M.op X0 X0) X4)) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq56 X3 X4 X4 X1 X2 X5
       have i₂ := eq59 X4 X0
       grind)
    | (have i₁ := eq56 X3 X4 X4 X1 X2 X5
       have i₂ := eq59 X0 X4
       grind)
    | exact superpose eq59 eq56
    | exact resolve eq56 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1020 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0
       have i₂ := eq59 (σ X0) X1
       grind)
    | (have i₁ := eq90 X0
       have i₂ := eq59 X0 (σ X0)
       grind)
    | exact superpose eq59 eq90
    | exact resolve eq90 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq12336 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq125 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12337 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq12336
    | exact resolve eq12336 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12336
  have eq12348 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq12337
       have r₂ := eq29
       grind)
    | exact resolve eq12337 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12337
  have eq12352 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq12348
  have eq12390 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq12352
    | exact resolve eq12352 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12352
  have eq12441 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq12390 eq125
    | exact resolve eq125 eq12390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq12390
  have eq12450 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq12441
  have eq12453 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq12450
       have r₂ := eq29
       grind)
    | exact resolve eq12450 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12450
  have eq12458 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq12453
  have eq12497 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12458
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq12458
    | exact resolve eq12458 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12458
  have eq12682 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq12497
       grind)
    | exact superpose eq12497 eq46
    | exact resolve eq46 eq12497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq12497
  have eq12698 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq22 eq12682
    | exact resolve eq12682 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12682
  have eq12743 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq12698 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq12698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12744 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq12743
  have eq12748 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq28 eq12744
    | exact resolve eq12744 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12744
  have eq12759 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq12748
       have r₂ := eq29
       grind)
    | exact resolve eq12748 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12748
  have eq12791 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq12759
  have eq12832 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28 eq12791
    | exact resolve eq12791 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12791
  have eq14105 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12832 eq12698
    | exact resolve eq12698 eq12832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12698 eq12832
  have eq14108 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq14105
  have eq14114 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq14108
       have r₂ := eq29
       grind)
    | exact resolve eq14108 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14108
  have eq14117 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq14114 eq31
    | exact resolve eq31 eq14114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq14114
  have eq14237 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq14117
    | exact resolve eq14117 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq14117
  have eq14238 : x = y := by grind
  clear eq14237
  have eq14771 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq14238
       grind)
    | exact superpose eq14238 eq20
    | exact resolve eq20 eq14238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq14772 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq14238
       grind)
    | exact superpose eq14238 eq26
    | exact resolve eq26 eq14238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq14238
  have eq14882 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq14772
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14772
    | exact resolve eq14772 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq14772
  have eq14883 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq14882 eq28
    | exact resolve eq28 eq14882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq14882
  have eq15004 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14771
       have i₂ := eq59 x X0
       grind)
    | (have i₁ := eq14771
       have i₂ := eq59 X0 x
       grind)
    | exact superpose eq59 eq14771
    | exact resolve eq14771 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq14771
  have eq15165 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14883 eq15004
    | exact resolve eq15004 eq14883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14883
  have eq15290 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq608 x X0 X1 x x (M.op x (M.op (M.op x x) x))
       have i₂ := eq15004 (M.op x (M.op (M.op x x) x))
       grind)
    | exact superpose eq15004 eq608
    | exact resolve eq608 eq15004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq15303 : ∀ X1 : G, (M.op x y) = (M.op X1 (M.op x y)) := by
    intro X1
    first
    | (have i₁ := eq15290 x X1
       have i₂ := eq15004 x
       grind)
    | exact superpose eq15004 eq15290
    | exact resolve eq15290 eq15004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15290
  have eq15422 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq15165 eq29
    | exact resolve eq29 eq15165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq15165
  have eq16429 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) := by grind
  clear eq15303
  have eq16528 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq16429
       have i₂ := eq15004 sF0
       grind)
    | exact superpose eq15004 eq16429
    | exact resolve eq16429 eq15004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16429
  have eq17913 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq16528 eq1020
    | (have j0 := eq1020 X0 (M.op x y)
       grind)
    | exact resolve eq1020 eq16528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020 eq16528
  have eq17916 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq17913 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17913
  have eq17922 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq22 eq17916
    | (have j0 := eq17916 X0
       grind)
    | exact resolve eq17916 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq17916
  have eq17931 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq17922 x
       have i₂ := eq15004 x
       grind)
    | exact superpose eq15004 eq17922
    | exact resolve eq17922 eq15004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15004 eq17922
  have eq17935 : False := by grind
  exact eq17935

/-- `Equation3506`: `x ◇ x = y ◇ ((z ◇ w) ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pyy_pxy_pyy_Equation3506 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) Law3506 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3506.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X3) X3)) := by
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
  clear eq22
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
  have eq54 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 X3) = (M.op X4 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 X3 X4 X5 X5
       have i₂ := eq14 X5 X0 X1 X2
       grind)
    | (have i₁ := eq14 X0 X1 X1 (M.op (M.op X2 X3) X3)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 x (M.op (M.op x x) x)
       have i₂ := eq14 X0 (M.op x (M.op (M.op x x) x)) x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x x x
       have i₂ := eq14 X1 x x x
       grind)
    | (have i₁ := eq14 X0 (M.op (M.op x x) x) x x
       have i₂ := eq14 (M.op (M.op x x) x) X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq57 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq57 X0 X1
       grind)
    | exact resolve eq12 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq105 x y
       grind)
    | exact superpose eq105 eq44
    | (have j1 := eq105 x y
       grind)
    | exact resolve eq44 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq131 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq121
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq121
    | exact resolve eq121 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq132 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq131
    | exact resolve eq131 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq434 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq1092 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq132 eq105
    | (have j0 := eq105 x (σ y)
       grind)
    | exact resolve eq105 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1093 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq1092
    | exact resolve eq1092 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092
  have eq1096 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1093
       have r₂ := eq27
       grind)
    | exact resolve eq1093 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq1100 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1096 eq13
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq1096
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq1096
       grind)
    | exact resolve eq13 eq1096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1096
  have eq1111 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq1100 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100
  have eq1235 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1111 eq132
    | exact resolve eq132 eq1111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq1240 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1111 eq434
    | exact resolve eq434 eq1111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434 eq1111
  have eq1241 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1235
  have eq1243 : ∀ X0 : G, y = (k X0 y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq29 eq1240
    | exact resolve eq1240 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240
  have eq1251 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq56 y X0 X1
       have i₂ := eq1241
       grind)
    | exact superpose eq1241 eq56
    | exact resolve eq56 eq1241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq2122 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq105 X0 y
       have i₂ := eq1243 X0
       grind)
    | exact superpose eq1243 eq105
    | (have j0 := eq105 X0 y
       grind)
    | exact resolve eq105 eq1243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243
  have eq2125 : ∀ X0 : G, y = (M.op y y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq2122 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2122
  have eq2326 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1251 X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1251
    | (have j0 := eq1251 X0 x
       grind)
    | exact resolve eq1251 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1251
  have eq2693 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1241
       have i₂ := eq2326 y
       grind)
    | exact superpose eq2326 eq1241
    | exact resolve eq1241 eq2326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241 eq2326
  have eq2696 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq2693
  have eq2705 : y = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2696 eq29
    | exact resolve eq29 eq2696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2696
  have eq2729 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq2705
    | exact resolve eq2705 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2705
  have eq2730 : y = (M.op x y) := by grind
  clear eq2729
  have eq2731 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq2730 eq20
    | exact resolve eq20 eq2730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2730
  have eq2752 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2731
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2731
    | exact resolve eq2731 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2731
  have eq3016 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2752 eq26
    | exact resolve eq26 eq2752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq3505 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have j0 := eq2125 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2125
  have eq3506 : y = (M.op y y) := by grind
  clear eq3505
  have eq3513 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq3506
       have i₂ := eq57 y X0
       grind)
    | (have i₁ := eq3506
       have i₂ := eq57 X0 y
       grind)
    | exact superpose eq57 eq3506
    | exact resolve eq3506 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq3519 : ∀ X0 : G, y ≠ y ∨ y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq3506
       grind)
    | exact superpose eq3506 eq13
    | (have r₁ := eq13 X0 y
       have r₂ := eq3506
       grind)
    | exact resolve eq13 eq3506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3506
  have eq3541 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq3519 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3519
  have eq3659 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq54 x x x X0 X1 (M.op x (M.op (M.op x x) x))
       have i₂ := eq3513 (M.op x (M.op (M.op x x) x))
       grind)
    | exact superpose eq3513 eq54
    | exact resolve eq54 eq3513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq3662 : ∀ X1 : G, y = (M.op X1 y) := by
    intro X1
    first
    | (have i₁ := eq3659 x X1
       have i₂ := eq3513 x
       grind)
    | exact superpose eq3513 eq3659
    | exact resolve eq3659 eq3513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3659
  have eq3739 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 y
       have i₂ := eq3541 (τ X0)
       grind)
    | exact superpose eq3541 eq34
    | exact resolve eq34 eq3541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq3541
  have eq3741 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3739 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3739
    | (have j0 := eq3739 X0
       grind)
    | exact resolve eq3739 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3739
  have eq3747 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq2752 eq3741
    | exact resolve eq3741 eq2752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2752 eq3741
  have eq3864 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq3747 eq105
    | (have j0 := eq105 X0 (σ (M.op x y))
       grind)
    | exact resolve eq105 eq3747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq3747
  have eq3868 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ y = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq3864 X0
       have i₂ := eq3513 sF1
       grind)
    | exact superpose eq3513 eq3864
    | (have j0 := eq3864 X0
       grind)
    | exact resolve eq3864 eq3513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3864
  have eq4645 : y = (σ (M.op x y)) ∨ y = (σ (M.op x y)) := by
    first
    | exact superpose eq3868 eq3513
    | exact resolve eq3513 eq3868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3513 eq3868
  have eq4669 : y = (σ (M.op x y)) := by grind
  clear eq4645
  have eq4729 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq4669 eq3016
    | exact resolve eq3016 eq4669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3016
  have eq4743 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4729
       have i₂ := eq3662 sF2
       grind)
    | exact superpose eq3662 eq4729
    | exact resolve eq4729 eq3662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3662 eq4729
  have eq4775 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq4743 eq27
    | exact resolve eq27 eq4743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq4743
  have eq4789 : False := by grind
  exact eq4789
