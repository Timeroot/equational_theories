import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,Y) else if X = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pyy_pyy_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq63 (σ X0)
       grind)
    | exact superpose eq63 eq15
    | exact resolve eq15 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq66
    | exact resolve eq66 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq66
  have eq396 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq404 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
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
  have eq413 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq396 X0 X1
       have i₂ := eq77 X1
       grind)
    | exact superpose eq77 eq396
    | (have j0 := eq396 X0 X1
       grind)
    | exact resolve eq396 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq960 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq413 x y
       grind)
    | exact superpose eq413 eq16
    | (have j1 := eq413 x y
       grind)
    | exact resolve eq16 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq965 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq413 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq2922 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq404 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq404
    | exact resolve eq404 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq2971 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2922 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2922
    | (have j0 := eq2922 X0 X1
       grind)
    | exact resolve eq2922 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2922
  have eq2976 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 X0) = (M.op X0 X0) ∨ X0 = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq2971 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq2971 X0 X1
       grind)
    | exact superpose eq2971 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq2971 (k X1 X0) (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq2971 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq2971 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq2971 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq12 eq2971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2971
  have eq3000 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2976 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2976
  have eq3055 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ X0 = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq3000 X1 X0
       grind)
    | exact superpose eq3000 eq10
    | (have j1 := eq3000 (k X0 X1) (τ (σ (M.op X0 X1)))
       grind)
    | exact resolve eq10 eq3000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3099 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3055 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq3055
    | (have j0 := eq3055 X0 X1
       grind)
    | exact resolve eq3055 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3055
  have eq3131 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3099 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3099
    | (have j0 := eq3099 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq3099 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3099
  have eq3289 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3131 X0 X1
       have i₂ := eq77 X1
       grind)
    | exact superpose eq77 eq3131
    | (have j0 := eq3131 X0 X1
       grind)
    | exact resolve eq3131 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3131
  have eq9176 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3289 x y
       grind)
    | exact superpose eq3289 eq16
    | (have j1 := eq3289 x y
       grind)
    | exact resolve eq16 eq3289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9253 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq9176
       have i₂ := eq3000 y x
       grind)
    | exact superpose eq3000 eq9176
    | (have j1 := eq3000 (σ (M.op x y)) (σ (M.op y y))
       grind)
    | (have r₁ := eq9176
       have r₂ := eq3000 y x
       grind)
    | (have r₁ := eq9176
       have r₂ := eq3000 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq9176
       have r₂ := eq3000 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq9176 eq3000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3000 eq9176
  have eq9254 : x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (k x y) = (M.op y y) := by grind
  clear eq9253
  have eq9435 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9254
       grind)
    | exact superpose eq9254 eq16
    | exact resolve eq16 eq9254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9254
  have eq9436 : (k x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq9435
       have r₂ := eq77 x
       grind)
    | exact resolve eq9435 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9435
  have eq9442 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq965 x y
       have i₂ := eq9436
       grind)
    | exact superpose eq9436 eq965
    | (have j0 := eq965 x y
       grind)
    | exact resolve eq965 eq9436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965 eq9436
  have eq9448 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq9442
  have eq9449 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq9448
  have eq9479 : (σ (k x y)) = (σ (M.op y y)) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3289 x y
       have i₂ := eq9449
       grind)
    | exact superpose eq9449 eq3289
    | (have j0 := eq3289 x y
       grind)
    | exact resolve eq3289 eq9449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3289 eq9449
  have eq9490 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq9479
  have eq9500 : y = (τ (σ x)) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq9490
       grind)
    | exact superpose eq9490 eq10
    | exact resolve eq10 eq9490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9490
  have eq9563 : x = y ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9500
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9500
    | exact resolve eq9500 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9500
  have eq9565 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9563
       grind)
    | exact superpose eq9563 eq16
    | exact resolve eq16 eq9563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9563
  have eq9566 : (σ (k x y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq9565
       have r₂ := eq77 x
       grind)
    | exact resolve eq9565 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9565
  have eq9568 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq9566
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq9566
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq9566 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9623 : x = y ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq9568
  have eq9661 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9623
       grind)
    | exact superpose eq9623 eq16
    | exact resolve eq16 eq9623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9623
  have eq9662 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq9661
       have r₂ := eq77 x
       grind)
    | exact resolve eq9661 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9661
  have eq9665 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k X0 y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq9662
       grind)
    | exact superpose eq9662 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq9662
       grind)
    | exact resolve eq12 eq9662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9662
  have eq10043 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have j0 := eq9665 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9665
  have eq10054 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9566
       have i₂ := eq10043
       grind)
    | exact superpose eq10043 eq9566
    | exact resolve eq9566 eq10043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9566 eq10043
  have eq10067 : (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq10054
  have eq10077 : (M.op y y) = (τ (σ (M.op x y))) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq10067
       grind)
    | exact superpose eq10067 eq10
    | exact resolve eq10 eq10067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10140 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10077
       have i₂ := eq10 (M.op x y)
       grind)
    | exact superpose eq10 eq10077
    | exact resolve eq10077 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10077
  have eq10143 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq10140
       grind)
    | exact superpose eq10140 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq10140
       grind)
    | exact resolve eq12 eq10140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10140
  have eq11291 : (M.op x y) = (k x y) := by
    first
    | (have j0 := eq10143 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10143
  have eq11318 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq960
       have i₂ := eq11291
       grind)
    | exact superpose eq11291 eq960
    | exact resolve eq960 eq11291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960 eq11291
  have eq11331 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by grind
  clear eq11318
  have eq11336 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11331
       have i₂ := eq10067
       grind)
    | exact superpose eq10067 eq11331
    | exact resolve eq11331 eq10067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10067 eq11331
  have eq11340 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq11336
       have r₂ := eq16
       grind)
    | exact resolve eq11336 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11336
  have eq11342 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11340
       grind)
    | exact superpose eq11340 eq16
    | exact resolve eq16 eq11340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11343 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq11340
       grind)
    | exact superpose eq11340 eq10
    | exact resolve eq10 eq11340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11340
  have eq11423 : x = y := by
    first
    | (have i₁ := eq11343
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11343
    | exact resolve eq11343 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11343
  have eq11424 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq11342
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq11342
    | exact resolve eq11342 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq11342
  have eq11429 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq11424
       have i₂ := eq11423
       grind)
    | exact superpose eq11423 eq11424
    | exact resolve eq11424 eq11423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11423 eq11424
  have eq11430 : False := by grind
  exact eq11430

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_y_pyx_y_pyx_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq265 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ y) (σ x)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
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
  have eq273 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq266 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq274 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq273 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq280 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq274 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq274 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq274 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq281 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq265
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq265 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq282 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq281
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq281
    | exact resolve eq281 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq403 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq280 X0 (τ X1)
       grind)
    | exact superpose eq280 eq17
    | (have j1 := eq280 X0 (τ X1)
       grind)
    | exact resolve eq17 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq409 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq280 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq775 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq403 (τ X0) X1
       grind)
    | exact superpose eq403 eq18
    | (have j1 := eq403 (τ X0) X1
       grind)
    | exact resolve eq18 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq403
  have eq780 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq775 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq775
    | (have j0 := eq775 X0 X1
       grind)
    | exact resolve eq775 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq793 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq780 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq780
    | (have j0 := eq780 X0 X1
       grind)
    | exact resolve eq780 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq796 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq793 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq793
    | (have j0 := eq793 X0 X1
       grind)
    | exact resolve eq793 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793
  have eq859 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq796 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq796
    | (have j0 := eq796 X1 (σ X0)
       grind)
    | exact resolve eq796 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796
  have eq1262 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq859 X0 X0
       have i₂ := eq280 X0 (σ X0)
       grind)
    | exact superpose eq280 eq859
    | (have j0 := eq859 X1 X0
       have j1 := eq280 X0 (σ X1)
       grind)
    | exact resolve eq859 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280 eq859
  have eq1292 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1262 X0 X1
       have j1 := eq409 (σ X1) X0
       grind)
    | (have r₁ := eq1262 X1 X1
       have r₂ := eq409 (σ X1) X1
       grind)
    | exact resolve eq1262 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409 eq1262
  have eq1465 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq1292 (σ X0) X1
       grind)
    | exact superpose eq1292 eq22
    | (have j1 := eq1292 (σ X0) X1
       grind)
    | exact resolve eq22 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1292
  have eq1472 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1465 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1465
    | (have j0 := eq1465 X0 X1
       grind)
    | exact resolve eq1465 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465
  have eq1488 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1472 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1472
    | (have j0 := eq1472 X0 X1
       grind)
    | exact resolve eq1472 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1472
  have eq1497 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1488 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1488
    | (have j0 := eq1488 X0 X1
       grind)
    | exact resolve eq1488 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488
  have eq1581 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1497 x y
       grind)
    | exact superpose eq1497 eq16
    | (have j1 := eq1497 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1497 x y
       grind)
    | exact resolve eq16 eq1497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497
  have eq1601 : x = (k y x) := by grind
  clear eq1581
  have eq1866 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq282
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq282
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq282 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1867 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op y x) ∨ (M.op x y) = (k y x) := by grind
  clear eq1866
  have eq1868 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq1867
       have r₂ := eq12 y x
       grind)
    | exact resolve eq1867 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1867
  have eq1869 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1868
       have i₂ := eq1601
       grind)
    | exact superpose eq1601 eq1868
    | exact resolve eq1868 eq1601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1868
  have eq1870 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1869
       have i₂ := eq1601
       grind)
    | exact superpose eq1601 eq1869
    | exact resolve eq1869 eq1601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869
  have eq1871 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq282
       have i₂ := eq1870
       grind)
    | exact superpose eq1870 eq282
    | exact resolve eq282 eq1870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282 eq1870
  have eq1883 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1871
  have eq1884 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1883
       have i₂ := eq1601
       grind)
    | exact superpose eq1601 eq1883
    | exact resolve eq1883 eq1601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1883
  have eq1885 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1884
  have eq1887 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1885
       grind)
    | exact superpose eq1885 eq16
    | exact resolve eq16 eq1885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1885
  have eq1916 : (σ x) ≠ (σ x) ∨ x = (M.op y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1887
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq1887
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq1887 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1917 : x = (M.op y x) ∨ (M.op x y) = (k y x) := by grind
  clear eq1916
  have eq1919 : (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq1917
       have r₂ := eq12 y x
       grind)
    | exact resolve eq1917 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1917
  have eq1920 : x = (M.op x y) := by
    first
    | (have i₁ := eq1919
       have i₂ := eq1601
       grind)
    | exact superpose eq1601 eq1919
    | exact resolve eq1919 eq1601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601 eq1919
  have eq1921 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1887
       have i₂ := eq1920
       grind)
    | exact superpose eq1920 eq1887
    | exact resolve eq1887 eq1920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1887 eq1920
  have eq1935 : False := by grind
  exact eq1935

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pxy_pxx_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq64 (σ X0)
       grind)
    | exact superpose eq64 eq15
    | exact resolve eq15 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq67
    | exact resolve eq67 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq67
  have eq409 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 X1) = (M.op X1 (τ X0)) := by
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
  have eq2863 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq409 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq409
    | exact resolve eq409 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq2910 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2863 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2863
    | (have j0 := eq2863 X0 X1
       grind)
    | exact resolve eq2863 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2863
  have eq2919 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq2910 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq2910 X0 X1
       grind)
    | exact superpose eq2910 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq2910 (M.op X1 X0) (k X1 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq2910 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq2910 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq2910 (M.op X1 X0) (M.op X1 X1)
       grind)
    | exact resolve eq12 eq2910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2910
  have eq2960 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2919 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2919
  have eq3060 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq2960 X1 X0
       grind)
    | exact superpose eq2960 eq10
    | (have j1 := eq2960 (k X0 X1) (τ (σ (M.op X0 X1)))
       grind)
    | exact resolve eq10 eq2960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2960
  have eq3102 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3060 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq3060
    | (have j0 := eq3060 X0 X1
       grind)
    | exact resolve eq3060 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3060
  have eq3103 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3102 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3102
  have eq3133 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq3103 X0 (τ X1)
       grind)
    | exact superpose eq3103 eq19
    | (have j1 := eq3103 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq3103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3153 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq3103 (σ X0) (σ X1)
       grind)
    | exact superpose eq3103 eq15
    | (have j1 := eq3103 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq3103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3103
  have eq3443 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3133 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3133
    | exact resolve eq3133 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3133
  have eq3496 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3443 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3443
    | (have j0 := eq3443 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq3443 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3443
  have eq3796 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3153 x y
       grind)
    | exact superpose eq3153 eq16
    | (have j1 := eq3153 x y
       grind)
    | exact resolve eq16 eq3153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3153
  have eq3816 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3796
       have i₂ := eq3496 y x
       grind)
    | exact superpose eq3496 eq3796
    | (have j1 := eq3496 (σ x) (σ y)
       grind)
    | (have r₁ := eq3796
       have r₂ := eq3496 y x
       grind)
    | (have r₁ := eq3796
       have r₂ := eq3496 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq3796
       have r₂ := eq3496 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3796 eq3496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3496 eq3796
  have eq3819 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq3816
  have eq3822 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3819
       grind)
    | exact superpose eq3819 eq16
    | exact resolve eq16 eq3819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3819
  have eq3823 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq3822
       have r₂ := eq78 x
       grind)
    | exact resolve eq3822 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3822
  have eq3888 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3823
       grind)
    | exact superpose eq3823 eq16
    | exact resolve eq16 eq3823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3889 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3823
       grind)
    | exact superpose eq3823 eq10
    | exact resolve eq10 eq3823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3823
  have eq3937 : x = y := by
    first
    | (have i₁ := eq3889
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3889
    | exact resolve eq3889 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3889
  have eq3938 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq3888
       have i₂ := eq78 x
       grind)
    | exact superpose eq78 eq3888
    | exact resolve eq3888 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq3888
  have eq3939 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq3938
       have i₂ := eq3937
       grind)
    | exact superpose eq3937 eq3938
    | exact resolve eq3938 eq3937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3937 eq3938
  have eq3940 : False := by grind
  exact eq3940

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pxy_pyx_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq87 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq87 X0 X1
       grind)
    | exact resolve eq13 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  clear eq87
  have eq187 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq182 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq192 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq183 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq183 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq183 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq193 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq187 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq187 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq187 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq187 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq202 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq192 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq192
    | (have j0 := eq192 X0 X1
       grind)
    | exact resolve eq192 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq203 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq202 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq204 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq193 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq193
    | (have j0 := eq193 X0 X1
       grind)
    | exact resolve eq193 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq205 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq204 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq210 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq205 X0 X1
       have j1 := eq203 X0 X1
       grind)
    | (have r₁ := eq205 X0 X1
       have r₂ := eq203 X0 X1
       grind)
    | exact resolve eq205 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203 eq205
  have eq211 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq210 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq210
    | exact resolve eq210 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq210 x y
       grind)
    | exact superpose eq210 eq16
    | exact resolve eq16 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq276 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq211 X0 (τ X1)
       grind)
    | exact superpose eq211 eq18
    | exact resolve eq18 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq211
  have eq293 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq276 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq276
    | exact resolve eq276 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq301 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq293 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq293
    | exact resolve eq293 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq321 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq222
       have i₂ := eq301 x y
       grind)
    | exact superpose eq301 eq222
    | exact resolve eq222 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq301
  have eq322 : False := by grind
  exact eq322

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyy_pxy_pyy_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq22 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq22 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq27 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq31 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq31 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq31 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq34 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq34 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq34 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq41 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq36 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq43 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 X0 X1
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq39
    | (have j0 := eq39 X0 X1
       grind)
    | exact resolve eq39 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq39
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq43 X0 X1
       grind)
    | (have r₁ := eq44 X0 X1
       have r₂ := eq43 X0 X1
       grind)
    | exact resolve eq44 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq44
  have eq87 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq41 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq91 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       have j1 := eq46 X0 X1
       grind)
    | (have r₁ := eq87 X0 X1
       have r₂ := eq46 X0 X1
       grind)
    | (have r₁ := eq87 X0 X0
       have r₂ := eq46 X0 X0
       grind)
    | exact resolve eq87 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq87
  have eq194 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq91 (σ X0) (σ X1)
       grind)
    | exact superpose eq91 eq15
    | exact resolve eq15 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq194 X0 X1
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq194
    | exact resolve eq194 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq194
  have eq203 : False := by grind
  exact eq203

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyx_pxx_pyx_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  clear eq19
  have eq72 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq101 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
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
  have eq476 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq9
    | (have j1 := eq72 X0
       grind)
    | exact resolve eq9 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq483 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq476 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq476 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq476 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq498 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq483 (σ X0)
       grind)
    | exact superpose eq483 eq15
    | exact resolve eq15 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq517 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq498 X0
       have i₂ := eq483 X0
       grind)
    | exact superpose eq483 eq498
    | exact resolve eq498 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483 eq498
  have eq793 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq101 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq1500 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (τ X1) X0) = X0 ∨ (τ X1) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X1) X0
       have i₂ := eq103 X0 X1
       grind)
    | exact superpose eq103 eq12
    | (have j1 := eq103 X0 X1
       grind)
    | (have r₁ := eq12 (τ X1) X0
       have r₂ := eq103 X0 X1
       grind)
    | (have r₁ := eq12 X0 (τ X1)
       have r₂ := eq103 (M.op (τ X1) X0) X1
       grind)
    | exact resolve eq12 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq1506 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1500 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1500
  have eq4176 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1506 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1506
    | exact resolve eq1506 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1506
  have eq4231 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4176 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4176
    | (have j0 := eq4176 X0 X1
       grind)
    | exact resolve eq4176 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4176
  have eq4275 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ X0 = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq4231 X1 X0
       grind)
    | exact superpose eq4231 eq10
    | (have j1 := eq4231 (k X1 X0) (τ (σ (M.op X0 X1)))
       grind)
    | exact resolve eq10 eq4231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4325 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4275 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq4275
    | (have j0 := eq4275 X0 X1
       grind)
    | exact resolve eq4275 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4275
  have eq4370 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ X1) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 X0
       have i₂ := eq4325 X0 (σ X1)
       grind)
    | exact superpose eq4325 eq29
    | (have j1 := eq4325 (k (σ X1) X0) X0
       grind)
    | exact resolve eq29 eq4325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4325
  have eq7257 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X1) X0
       have i₂ := eq4370 (σ X0) X1
       grind)
    | exact superpose eq4370 eq23
    | (have j1 := eq4370 (σ X1) X0
       grind)
    | exact resolve eq23 eq4370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq4370
  have eq7318 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7257 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq7257
    | (have j0 := eq7257 X0 X1
       grind)
    | exact resolve eq7257 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7257
  have eq7352 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7318 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7318
    | (have j0 := eq7318 X0 X1
       grind)
    | exact resolve eq7318 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7318
  have eq7361 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7352 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7352
    | (have j0 := eq7352 X0 X1
       grind)
    | exact resolve eq7352 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7352
  have eq7565 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq7361 X1 X0
       grind)
    | exact superpose eq7361 eq11
    | (have j1 := eq7361 X1 X0
       grind)
    | exact resolve eq11 eq7361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7361
  have eq8471 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7565 y x
       grind)
    | exact superpose eq7565 eq16
    | (have j1 := eq7565 y x
       grind)
    | exact resolve eq16 eq7565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7565
  have eq8502 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8471
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq8471
    | (have j1 := eq14 x (M.op x y)
       grind)
    | (have r₁ := eq8471
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq8471
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq8471 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8503 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k y x) := by
    first
    | (have i₁ := eq8471
       have i₂ := eq4231 y x
       grind)
    | exact superpose eq4231 eq8471
    | (have j1 := eq4231 x (k y x)
       grind)
    | (have r₁ := eq8471
       have r₂ := eq4231 y x
       grind)
    | (have r₁ := eq8471
       have r₂ := eq4231 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq8471
       have r₂ := eq4231 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq8471 eq4231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4231 eq8471
  have eq8506 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8503
  have eq8507 : x = y ∨ (σ x) = (σ y) ∨ x = (k y x) := by grind
  clear eq8506
  have eq8508 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8502
  have eq8509 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq8508
  have eq8513 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8507
       grind)
    | exact superpose eq8507 eq16
    | exact resolve eq16 eq8507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8507
  have eq8514 : x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8513
       have r₂ := eq517 x
       grind)
    | exact resolve eq8513 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8513
  have eq8518 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq793 x y
       have i₂ := eq8514
       grind)
    | exact superpose eq8514 eq793
    | (have j0 := eq793 x y
       grind)
    | exact resolve eq793 eq8514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793 eq8514
  have eq8525 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8518
  have eq8526 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq8525
  have eq8624 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8509
       grind)
    | exact superpose eq8509 eq16
    | exact resolve eq16 eq8509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8509
  have eq8625 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8624
       have r₂ := eq517 x
       grind)
    | exact resolve eq8624 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8624
  have eq8637 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8526
       grind)
    | exact superpose eq8526 eq16
    | exact resolve eq16 eq8526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8526
  have eq8661 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8637
       have i₂ := eq8625
       grind)
    | exact superpose eq8625 eq8637
    | exact resolve eq8637 eq8625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8625 eq8637
  have eq8662 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq8661
  have eq8663 : (σ x) = (σ y) := by grind
  clear eq8662
  have eq8664 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8663
       grind)
    | exact superpose eq8663 eq16
    | exact resolve eq16 eq8663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8665 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq8663
       grind)
    | exact superpose eq8663 eq10
    | exact resolve eq10 eq8663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8663
  have eq8726 : x = y := by
    first
    | (have i₁ := eq8665
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8665
    | exact resolve eq8665 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8665
  have eq8727 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8664
       have i₂ := eq517 x
       grind)
    | exact superpose eq517 eq8664
    | exact resolve eq8664 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517 eq8664
  have eq8730 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8727
       have i₂ := eq8726
       grind)
    | exact superpose eq8726 eq8727
    | exact resolve eq8727 eq8726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8726 eq8727
  have eq8731 : False := by grind
  exact eq8731

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_pyy_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
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
  clear eq18
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
  clear eq19
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq64 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq272 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq273 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (τ X0) (τ X1)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq14
    | (have j0 := eq14 (τ X0) (τ X1)
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5821 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq272 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq272
    | (have j0 := eq272 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq272 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5822 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq5875 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq272 X0 X1
       grind)
    | exact superpose eq272 eq10
    | (have j1 := eq272 X0 X1
       grind)
    | exact resolve eq10 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6339 : ∀ X0 : G, (M.op (τ (k X0 X0)) (τ X0)) = (k (τ (k X0 X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq6342 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq273 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6343 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq273 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq6344 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq6343 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6343
  have eq6346 : ∀ X0 : G, (M.op (τ (k X0 X0)) (τ X0)) = (k (τ (k X0 X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq6339 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6339
  have eq6355 : ∀ X0 : G, (M.op (τ (k X0 X0)) (τ X0)) = (τ (k (k X0 X0) X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq6346 X0
       have i₂ := eq32 X0 (k X0 X0)
       grind)
    | exact superpose eq32 eq6346
    | (have j0 := eq6346 X0
       grind)
    | exact resolve eq6346 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq6346
  have eq6375 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq6344 (σ X0)
       have i₂ := eq29 X0 (σ X0)
       grind)
    | exact superpose eq29 eq6344
    | (have j0 := eq6344 (σ X0)
       grind)
    | exact resolve eq6344 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq6344
  have eq6395 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq6375 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6375
    | (have j0 := eq6375 X0
       grind)
    | exact resolve eq6375 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6375
  have eq6412 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6395 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6395
    | (have j0 := eq6395 X0
       grind)
    | exact resolve eq6395 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6395
  have eq6450 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq6412 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq6412
    | (have j0 := eq6412 (σ X0)
       grind)
    | exact resolve eq6412 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6412
  have eq6453 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6450 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq6450
    | (have j0 := eq6450 X0
       have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq6450 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6450
  have eq6472 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq6453 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6453
  have eq6700 : ∀ X0 : G, (M.op (τ (σ (k X0 X0))) (τ (σ X0))) = (τ (k (σ (k X0 X0)) (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq6355 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq6355
    | (have j0 := eq6355 (σ X0)
       grind)
    | exact resolve eq6355 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6355
  have eq6767 : ∀ X0 : G, (M.op (τ (σ (k X0 X0))) (τ (σ X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq6700 X0
       have i₂ := eq23 (σ (k X0 X0)) X0
       grind)
    | exact superpose eq23 eq6700
    | (have j0 := eq6700 X0
       grind)
    | exact resolve eq6700 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq6700
  have eq6787 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq6767 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq6767
    | (have j0 := eq6767 X0
       grind)
    | exact resolve eq6767 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6767
  have eq6803 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq6787 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6787
    | (have j0 := eq6787 X0
       grind)
    | exact resolve eq6787 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6787
  have eq6819 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6803 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6803
    | (have j0 := eq6803 X0
       grind)
    | exact resolve eq6803 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6803
  have eq6874 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq6819 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq6819
    | (have j0 := eq6819 (σ X0)
       grind)
    | exact resolve eq6819 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6819
  have eq7005 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq6874 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq6874
    | (have j0 := eq6874 X0
       grind)
    | exact resolve eq6874 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6874
  have eq7127 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7005 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq7005
    | (have j0 := eq7005 X0
       have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq7005 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7005
  have eq7220 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7127 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7127
  have eq7251 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq7220
  have eq9306 : ∀ X0 : G, (τ X0) ≠ (τ (M.op (M.op X0 X0) X0)) ∨ (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    grind
  have eq9308 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ X1)) ∨ (τ (σ X1)) = (M.op (τ (σ X0)) (τ (σ X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6342 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6342
    | (have j0 := eq6342 (σ X0) (σ X1)
       grind)
    | exact resolve eq6342 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6342
  have eq9375 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X0)) (τ (σ X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9308 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq9308
    | (have j0 := eq9308 X0 X1
       grind)
    | exact resolve eq9308 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9308
  have eq9403 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X0)) (τ (σ X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9375 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq9375
    | (have j0 := eq9375 X0 X1
       grind)
    | exact resolve eq9375 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9375
  have eq9430 : ∀ X0 X1 : G, (M.op (τ (σ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9403 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9403
    | (have j0 := eq9403 X0 X1
       grind)
    | exact resolve eq9403 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9403
  have eq9456 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9430 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9430
    | (have j0 := eq9430 X0 X1
       grind)
    | exact resolve eq9430 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9430
  have eq9477 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9456 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9456
    | (have j0 := eq9456 X0 X1
       grind)
    | exact resolve eq9456 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9456
  have eq9494 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9477 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9477
    | (have j0 := eq9477 X0 X1
       grind)
    | exact resolve eq9477 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9477
  have eq9524 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9494 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9494
    | (have j0 := eq9494 (σ X0) (σ X1)
       grind)
    | exact resolve eq9494 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9494
  have eq15094 : ∀ X0 : G, (σ X0) ≠ (σ (M.op (M.op X0 X0) X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq5822 X0
       grind)
    | exact superpose eq5822 eq13
    | (have j0 := eq13 (σ (M.op X0 X0)) (σ X0)
       have j1 := eq5822 X0
       grind)
    | (have r₁ := eq13 (σ (M.op X0 X0)) (σ X0)
       have r₂ := eq5822 X0
       grind)
    | exact resolve eq13 eq5822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15096 : ∀ X0 : G, (σ X0) ≠ (σ (M.op (M.op X0 X0) X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq5822 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5822
  have eq15097 : ∀ X0 : G, (σ X0) ≠ (σ (M.op (M.op X0 X0) X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq15094 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15094
  have eq15106 : ∀ X0 : G, (σ X0) ≠ (σ (M.op (M.op X0 X0) X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq15097 X0
       have j1 := eq13 (σ (M.op X0 X0)) (σ X0)
       grind)
    | (have r₁ := eq15097 X0
       have r₂ := eq13 (σ (M.op X0 X0)) (σ X0)
       grind)
    | exact resolve eq15097 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15097
  have eq15118 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (M.op X0 X0) X0)) ∨ (σ X0) ≠ (σ (M.op (M.op X0 X0) X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15106 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq15106
    | (have j0 := eq15106 X0
       grind)
    | exact resolve eq15106 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15106
  have eq15125 : ∀ X0 : G, (σ X0) ≠ (σ (M.op (M.op X0 X0) X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq15118
  have eq19156 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5821 x y
       grind)
    | exact superpose eq5821 eq16
    | (have j1 := eq5821 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq5821 x y
       grind)
    | exact resolve eq16 eq5821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19171 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq5821 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5821
  have eq19185 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq19156
  have eq19327 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19185
       grind)
    | exact superpose eq19185 eq16
    | exact resolve eq16 eq19185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19330 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq19185
       grind)
    | exact superpose eq19185 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq19185
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq19185
       grind)
    | exact resolve eq13 eq19185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19331 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ y)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9 (σ y) (σ x)
       have i₂ := eq19185
       grind)
    | exact superpose eq19185 eq9
    | exact resolve eq9 eq19185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19185
  have eq19332 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq19330
  have eq19333 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq19332
  have eq19335 : (M.op (σ y) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq19333
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq19333
    | exact resolve eq19333 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19333
  have eq19336 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14 eq19335
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq19335 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19335
  have eq19365 : (τ (σ (M.op x y))) = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq5875 y y
       have i₂ := eq19336
       grind)
    | exact superpose eq19336 eq5875
    | (have j0 := eq5875 x y
       grind)
    | exact resolve eq5875 eq19336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5875
  have eq19383 : (τ (σ (M.op x y))) = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq19365
  have eq19397 : (τ (σ (M.op x y))) = (k y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq19383
       have r₂ := eq19327
       grind)
    | exact resolve eq19383 eq19327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19383
  have eq19429 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq19397
       have i₂ := eq10 (M.op x y)
       grind)
    | exact superpose eq10 eq19397
    | exact resolve eq19397 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19397
  have eq19476 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq19429
  have eq19499 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq19476
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq19476
    | exact resolve eq19476 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19476
  have eq19528 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14 eq19499
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq19499 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19499
  have eq19547 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq19528
       have r₂ := eq16
       grind)
    | exact resolve eq19528 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19528
  have eq19567 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq272 y y
       have i₂ := eq19547
       grind)
    | exact superpose eq19547 eq272
    | (have j0 := eq272 y y
       grind)
    | exact resolve eq272 eq19547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq19571 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9524 y y
       have i₂ := eq19547
       grind)
    | exact superpose eq19547 eq9524
    | (have j0 := eq9524 y y
       grind)
    | exact resolve eq9524 eq19547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19547
  have eq19574 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq19571
  have eq19577 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq19567
  have eq19581 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq19327 eq19574
    | exact resolve eq19574 eq19327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19327 eq19574
  have eq19582 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq19336 eq19577
    | exact resolve eq19577 eq19336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19336 eq19577
  have eq348545 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9 (σ y) (σ y)
       have i₂ := eq19331
       grind)
    | exact superpose eq19331 eq9
    | exact resolve eq9 eq19331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19331
  have eq348579 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq19582
       have i₂ := eq348545
       grind)
    | exact superpose eq348545 eq19582
    | exact resolve eq19582 eq348545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19582
  have eq348606 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq348545
  have eq348610 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq348579
  have eq348644 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq348610
       have r₂ := eq19581
       grind)
    | exact resolve eq348610 eq19581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19581 eq348610
  have eq348677 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq348644
       have r₂ := eq348606
       grind)
    | exact resolve eq348644 eq348606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348606 eq348644
  have eq348814 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq348677
  have eq348861 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq348814
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq348814
    | exact resolve eq348814 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348814
  have eq348907 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14 eq348861
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq348861 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348861
  have eq348947 : y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq348907
       have r₂ := eq16
       grind)
    | exact resolve eq348907 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348907
  have eq348965 : y = (M.op y (M.op y (M.op y y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq348947
       grind)
    | exact superpose eq348947 eq9
    | exact resolve eq9 eq348947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348966 : y ≠ y ∨ x = (M.op y y) ∨ (M.op y y) = (k x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq348947
       grind)
    | exact superpose eq348947 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq348947
       grind)
    | exact resolve eq13 eq348947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348973 : y ≠ y ∨ x = (M.op y y) ∨ (M.op y y) = (k x y) := by grind
  clear eq348966
  have eq348974 : (M.op y y) = (k x y) ∨ x = (M.op y y) := by grind
  clear eq348973
  have eq349708 : y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9 y y
       have i₂ := eq348965
       grind)
    | exact superpose eq348965 eq9
    | exact resolve eq9 eq348965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348965
  have eq349729 : y = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq349708 eq348974
    | exact resolve eq348974 eq349708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348974
  have eq349735 : (σ y) ≠ (σ (M.op y y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq15125 y
       have i₂ := eq349708
       grind)
    | exact superpose eq349708 eq15125
    | (have j0 := eq15125 y
       grind)
    | exact resolve eq15125 eq349708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15125
  have eq349743 : x ≠ y ∨ x = (M.op y y) := by grind
  have eq349754 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq6472 eq349735
    | (have j1 := eq6472 y
       grind)
    | exact resolve eq349735 eq6472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6472 eq349735
  have eq349755 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq349754
  have eq349773 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq349708 eq349755
    | exact resolve eq349755 eq349708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349708 eq349755
  have eq349774 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq349773
  have eq349814 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9524 x y
       have i₂ := eq349729
       grind)
    | exact superpose eq349729 eq9524
    | (have j0 := eq9524 x y
       grind)
    | exact resolve eq9524 eq349729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9524
  have eq349824 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq349814
  have eq349833 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq349774
  have eq350746 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq349824
       grind)
    | exact superpose eq349824 eq16
    | exact resolve eq16 eq349824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349824
  have eq350766 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq348947 eq350746
    | exact resolve eq350746 eq348947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348947 eq350746
  have eq350767 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq350766
  have eq350806 : x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq350767 eq349833
    | exact resolve eq349833 eq350767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349833
  have eq350809 : (τ (M.op (σ x) (σ y))) = (k (τ (σ x)) y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq64 y
       have i₂ := eq350767
       grind)
    | exact superpose eq350767 eq64
    | exact resolve eq64 eq350767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq350928 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq350809
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq350809
    | exact resolve eq350809 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350809
  have eq350970 : y = (τ (M.op (σ x) (σ y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq349729 eq350928
    | exact resolve eq350928 eq349729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349729 eq350928
  have eq351004 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq350806 eq350767
    | exact resolve eq350767 eq350806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350767
  have eq351013 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq7251 y
       have i₂ := eq350806
       grind)
    | exact superpose eq350806 eq7251
    | (have j0 := eq7251 y
       grind)
    | exact resolve eq7251 eq350806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7251
  have eq351036 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq351013
       have r₂ := eq16
       grind)
    | exact resolve eq351013 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351013
  have eq352045 : y = (τ (M.op (σ x) (σ x))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq350806 eq350970
    | exact resolve eq350970 eq350806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350806 eq350970
  have eq352046 : y = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq351004 eq352045
    | exact resolve eq352045 eq351004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351004 eq352045
  have eq352047 : x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq352046
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq352046
    | exact resolve eq352046 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352046
  have eq352048 : x = (M.op y y) := by
    first
    | (have r₁ := eq352047
       have r₂ := eq349743
       grind)
    | exact resolve eq352047 eq349743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349743 eq352047
  have eq352075 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq19171 y y
       have i₂ := eq352048
       grind)
    | exact superpose eq352048 eq19171
    | (have j0 := eq19171 y y
       grind)
    | exact resolve eq19171 eq352048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19171
  have eq352078 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq352075
  have eq352080 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq352078
       have r₂ := eq351036
       grind)
    | exact resolve eq352078 eq351036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351036 eq352078
  have eq352128 : (τ (σ y)) ≠ (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq9306 (σ y)
       have i₂ := eq352080
       grind)
    | exact superpose eq352080 eq9306
    | exact resolve eq9306 eq352080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9306
  have eq352140 : (τ (σ y)) ≠ (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ x = y := by grind
  clear eq352128
  have eq352155 : y ≠ (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq352140
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq352140
    | exact resolve eq352140 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352140
  have eq352184 : y = (M.op y y) ∨ y ≠ (τ (M.op (σ y) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq352155
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq352155
    | exact resolve eq352155 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352155
  have eq352206 : x = y ∨ y ≠ (τ (M.op (σ y) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq352184
       have i₂ := eq352048
       grind)
    | exact superpose eq352048 eq352184
    | exact resolve eq352184 eq352048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352184
  have eq352207 : x = y ∨ y ≠ (τ (M.op (σ y) (σ y))) := by grind
  clear eq352206
  have eq352228 : x = y ∨ y ≠ (τ (σ y)) := by
    first
    | exact superpose eq352080 eq352207
    | exact resolve eq352207 eq352080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352080 eq352207
  have eq352247 : x = y := by
    first
    | (have r₁ := eq352228
       have r₂ := eq10 y
       grind)
    | exact resolve eq352228 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352228
  have eq352267 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq352247
       grind)
    | exact superpose eq352247 eq16
    | exact resolve eq16 eq352247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352268 : x = (M.op x x) := by
    first
    | (have i₁ := eq352048
       have i₂ := eq352247
       grind)
    | exact superpose eq352247 eq352048
    | exact resolve eq352048 eq352247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352048 eq352247
  have eq352275 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq15096 x
       have i₂ := eq352268
       grind)
    | exact superpose eq352268 eq15096
    | exact resolve eq15096 eq352268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15096
  have eq352284 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq352275
  have eq352296 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq352284
       have i₂ := eq352268
       grind)
    | exact superpose eq352268 eq352284
    | exact resolve eq352284 eq352268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352284
  have eq352297 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq352296
  have eq352674 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq352267
       have i₂ := eq352268
       grind)
    | exact superpose eq352268 eq352267
    | exact resolve eq352267 eq352268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352267 eq352268
  have eq352675 : False := by grind
  exact eq352675

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq385 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
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
  clear eq345
  have eq418 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq385 X0 X1
       grind)
    | exact superpose eq385 eq9
    | (have j1 := eq385 X0 X1
       grind)
    | exact resolve eq9 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq618 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq418 X0 X1
       grind)
    | exact superpose eq418 eq9
    | (have j1 := eq418 X0 X1
       grind)
    | exact resolve eq9 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq624 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq618 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq618 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq618 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq639 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq624 (σ X1) (σ X0)
       grind)
    | exact superpose eq624 eq15
    | exact resolve eq15 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq666 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq639 X0 X1
       have i₂ := eq624 X1 X0
       grind)
    | exact superpose eq624 eq639
    | exact resolve eq639 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624 eq639
  have eq1005 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq666 x y
       grind)
    | exact superpose eq666 eq16
    | (have r₁ := eq16
       have r₂ := eq666 x y
       grind)
    | exact resolve eq16 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq1021 : False := by grind
  exact eq1021
