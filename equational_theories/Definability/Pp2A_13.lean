import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2291`: `x = (y ◇ (x ◇ (x ◇ x))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation2291 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2291 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2291.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq443 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq458 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  clear eq19
  have eq461 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq484 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq461 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq461
    | (have j0 := eq461 X0 X1
       grind)
    | exact resolve eq461 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq669 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq484 x y
       grind)
    | exact superpose eq484 eq16
    | (have j1 := eq484 x y
       grind)
    | exact resolve eq16 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq675 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq484 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq3709 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq458 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq458
    | exact resolve eq458 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458
  have eq3771 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3709 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3709
    | (have j0 := eq3709 X0 X1
       grind)
    | exact resolve eq3709 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3709
  have eq7170 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq669
       have i₂ := eq3771 y x
       grind)
    | exact superpose eq3771 eq669
    | (have j1 := eq3771 y x
       grind)
    | (have r₁ := eq669
       have r₂ := eq3771 y x
       grind)
    | (have r₁ := eq669
       have r₂ := eq3771 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq669
       have r₂ := eq3771 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq669 eq3771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669 eq3771
  have eq7171 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by grind
  clear eq7170
  have eq7183 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq675 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq675
    | (have j0 := eq675 (τ X0) (τ X1)
       grind)
    | exact resolve eq675 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq7250 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7183 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq7183
    | (have j0 := eq7183 X0 X1
       grind)
    | exact resolve eq7183 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7183
  have eq7285 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7250 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq7250
    | (have j0 := eq7250 X0 X1
       grind)
    | exact resolve eq7250 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7250
  have eq7317 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7285 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7285
    | (have j0 := eq7285 X0 X1
       grind)
    | exact resolve eq7285 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7285
  have eq7343 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7317 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7317
    | (have j0 := eq7317 X0 X1
       grind)
    | exact resolve eq7317 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7317
  have eq7362 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7343 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq7343
    | (have j0 := eq7343 X0 X1
       grind)
    | exact resolve eq7343 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq7343
  have eq7379 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7362 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7362
    | (have j0 := eq7362 X0 X1
       grind)
    | exact resolve eq7362 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7362
  have eq7392 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7379 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7379
    | (have j0 := eq7379 X0 X1
       grind)
    | exact resolve eq7379 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7379
  have eq16368 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq7171
       grind)
    | exact superpose eq7171 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq7171
       grind)
    | exact resolve eq13 eq7171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7171
  have eq16369 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq16368
  have eq16370 : x = y ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq16369
  have eq16544 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16370
       grind)
    | exact superpose eq16370 eq16
    | exact resolve eq16 eq16370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16370
  have eq16545 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op x x) := by
    first
    | (have r₁ := eq16544
       have r₂ := eq22 x
       grind)
    | exact resolve eq16544 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16544
  have eq16548 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq443 x (σ y)
       have i₂ := eq16545
       grind)
    | exact superpose eq16545 eq443
    | (have j0 := eq443 x (σ y)
       grind)
    | (have r₁ := eq443 x (σ y)
       have r₂ := eq16545
       grind)
    | exact resolve eq443 eq16545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16545
  have eq16555 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by grind
  clear eq16548
  have eq16556 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by grind
  clear eq16555
  have eq16559 : (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16556
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq16556
    | exact resolve eq16556 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16556
  have eq16568 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq675 x y
       have i₂ := eq16559
       grind)
    | exact superpose eq16559 eq675
    | (have j0 := eq675 x y
       grind)
    | (have r₁ := eq675 x y
       have r₂ := eq16559
       grind)
    | exact resolve eq675 eq16559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16559
  have eq16590 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq16568
  have eq16591 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq16590
  have eq16595 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq675 x y
       grind)
    | (have r₁ := eq16591
       have r₂ := eq675 x y
       grind)
    | exact resolve eq16591 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675 eq16591
  have eq16598 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16595
       grind)
    | exact superpose eq16595 eq16
    | exact resolve eq16 eq16595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16599 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq443 x (σ y)
       have i₂ := eq16595
       grind)
    | exact superpose eq16595 eq443
    | (have j0 := eq443 x (σ y)
       grind)
    | (have r₁ := eq443 x (σ y)
       have r₂ := eq16595
       grind)
    | exact resolve eq443 eq16595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443 eq16595
  have eq16606 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq16599
  have eq16607 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq16606
  have eq16610 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16607
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq16607
    | exact resolve eq16607 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16607
  have eq16617 : y = (τ (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq16610
       grind)
    | exact superpose eq16610 eq10
    | exact resolve eq10 eq16610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16610
  have eq16796 : x = y ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16617
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq16617
    | exact resolve eq16617 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16617
  have eq16798 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16796
       grind)
    | exact superpose eq16796 eq16
    | exact resolve eq16 eq16796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16796
  have eq16799 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq16798
       have r₂ := eq22 x
       grind)
    | exact resolve eq16798 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16798
  have eq16809 : (k x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq16799
       grind)
    | exact superpose eq16799 eq10
    | exact resolve eq10 eq16799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16799
  have eq16989 : (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq16809
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq16809
    | exact resolve eq16809 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16809
  have eq17013 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq7392 x y
       have i₂ := eq16989
       grind)
    | exact superpose eq16989 eq7392
    | (have j0 := eq7392 x y
       grind)
    | (have r₁ := eq7392 x y
       have r₂ := eq16989
       grind)
    | exact resolve eq7392 eq16989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7392 eq16989
  have eq17016 : (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq17013
  have eq17020 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16598
       have i₂ := eq17016
       grind)
    | exact superpose eq17016 eq16598
    | exact resolve eq16598 eq17016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16598 eq17016
  have eq17026 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq17020
  have eq17027 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17026
       grind)
    | exact superpose eq17026 eq16
    | exact resolve eq16 eq17026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17026
  have eq17030 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq17027
       have r₂ := eq22 x
       grind)
    | exact resolve eq17027 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17027
  have eq17031 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17030
       grind)
    | exact superpose eq17030 eq16
    | exact resolve eq16 eq17030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17032 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq17030
       grind)
    | exact superpose eq17030 eq10
    | exact resolve eq10 eq17030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17030
  have eq17211 : x = y := by
    first
    | (have i₁ := eq17032
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq17032
    | exact resolve eq17032 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17032
  have eq17212 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq17031
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq17031
    | exact resolve eq17031 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq17031
  have eq17213 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq17212
       have i₂ := eq17211
       grind)
    | exact superpose eq17211 eq17212
    | exact resolve eq17212 eq17211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17211 eq17212
  have eq17214 : False := by grind
  exact eq17214

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyx_x_pxy_x_pyx_Equation2300 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
  have eq424 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq22
    | (have j1 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq22 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq428 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq3394 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq424 X0 X1
       grind)
    | exact superpose eq424 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq424 X1 X0
       grind)
    | (have r₁ := eq13 X1 (σ X0)
       have r₂ := eq424 X0 X1
       grind)
    | exact resolve eq13 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3421 : ∀ X0 X1 : G, (M.op X1 (σ X0)) ≠ X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq424 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq3422 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq3394 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3394
  have eq3430 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op (σ X1) X0)) ∨ (k X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq3422 X0 X1
       have j1 := eq3421 X1 X0
       grind)
    | (have r₁ := eq3422 X1 X0
       have r₂ := eq3421 X0 X1
       grind)
    | exact resolve eq3422 eq3421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3421 eq3422
  have eq3739 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq428 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq25374 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3430 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3430
    | exact resolve eq3430 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3430
  have eq25511 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25374 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq25374
    | (have j0 := eq25374 X0 X1
       grind)
    | exact resolve eq25374 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25374
  have eq25528 : ∀ X0 X1 : G, (M.op (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq25511 (τ X0) (τ X1)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq25511
    | (have j0 := eq25511 (τ X0) (τ X1)
       grind)
    | exact resolve eq25511 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25511
  have eq27878 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3739 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq3739
    | (have j0 := eq3739 (τ X1) (τ X0)
       grind)
    | exact resolve eq3739 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27993 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq27878 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq27878
    | (have j0 := eq27878 X0 X1
       grind)
    | exact resolve eq27878 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27878
  have eq28044 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq27993 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27993
    | (have j0 := eq27993 X0 X1
       grind)
    | exact resolve eq27993 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27993
  have eq28083 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28044 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28044
    | (have j0 := eq28044 X0 X1
       grind)
    | exact resolve eq28044 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28044
  have eq28108 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28083 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq28083
    | (have j0 := eq28083 X0 X1
       grind)
    | exact resolve eq28083 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28083
  have eq28129 : ∀ X0 X1 : G, (M.op X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28108 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28108
    | (have j0 := eq28108 X0 X1
       grind)
    | exact resolve eq28108 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28108
  have eq28146 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28129 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28129
    | (have j0 := eq28129 X0 X1
       grind)
    | exact resolve eq28129 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28129
  have eq863832 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) ≠ (M.op (τ X0) (τ X1)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (τ (k X1 X0)) ∨ (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X1) (τ X0)
       have i₂ := eq25528 X0 X1
       grind)
    | (have i₁ := eq12 (τ X0) (τ X1)
       have i₂ := eq25528 X0 X1
       grind)
    | exact superpose eq25528 eq12
    | (have j1 := eq25528 X1 X0
       grind)
    | (have r₁ := eq12 (τ X0) (τ X1)
       have r₂ := eq25528 X0 X1
       grind)
    | (have r₁ := eq12 (τ X1) (τ X0)
       have r₂ := eq25528 X0 X1
       grind)
    | exact resolve eq12 eq25528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25528
  have eq863869 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (τ (k X1 X0)) ∨ (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq863832 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863832
  have eq863900 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (τ (k X1 X0)) ∨ (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq863869 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq863869
    | (have j0 := eq863869 X0 X1
       grind)
    | exact resolve eq863869 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq863869
  have eq864117 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (τ (k (σ X0) X1)) = X0 ∨ (τ (τ (k (σ X0) X1))) = (τ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq863900 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq863900
    | exact resolve eq863900 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863900
  have eq864742 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ (k (σ X0) X1)) = X0 ∨ (τ (τ (k (σ X0) X1))) = (τ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq864117 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq864117
    | (have j0 := eq864117 X0 X1
       grind)
    | exact resolve eq864117 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864117
  have eq864859 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ (τ (k (σ X0) X1))) = (τ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq864742 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq864742
    | (have j0 := eq864742 X0 X1
       grind)
    | exact resolve eq864742 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864742
  have eq864946 : ∀ X0 X1 : G, (τ (k X0 (τ X1))) = (τ (M.op (τ X1) X0)) ∨ (k X0 (τ X1)) = X0 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq864859 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq864859
    | (have j0 := eq864859 X0 X1
       grind)
    | exact resolve eq864859 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864859
  have eq865244 : ∀ X0 X1 : G, (k X1 (τ X0)) = (σ (τ (M.op (τ X0) X1))) ∨ (k X1 (τ X0)) = X1 ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 (τ X0))
       have i₂ := eq864946 X1 X0
       grind)
    | exact superpose eq864946 eq11
    | (have j1 := eq864946 X1 X0
       grind)
    | exact resolve eq11 eq864946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864946
  have eq867151 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k X1 (τ X0)) = X1 ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq865244 X0 X1
       have i₂ := eq11 (M.op (τ X0) X1)
       grind)
    | exact superpose eq11 eq865244
    | (have j0 := eq865244 X0 X1
       grind)
    | exact resolve eq865244 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865244
  have eq867152 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq867151 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867151
  have eq867217 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq867152 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq867152
    | exact resolve eq867152 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq867375 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq867152 X0 X1
       grind)
    | exact superpose eq867152 eq18
    | (have j1 := eq867152 X0 X1
       grind)
    | exact resolve eq18 eq867152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq867152
  have eq869520 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq867217 (σ X0) X1
       grind)
    | exact superpose eq867217 eq22
    | (have j1 := eq867217 (σ X0) X1
       grind)
    | exact resolve eq22 eq867217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq867217
  have eq871786 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq867375 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq867375
    | exact resolve eq867375 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867375
  have eq872228 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq871786 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq871786
    | (have j0 := eq871786 X0 X1
       grind)
    | exact resolve eq871786 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871786
  have eq873833 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq869520 X1 (σ X0)
       grind)
    | exact superpose eq869520 eq28
    | (have j1 := eq869520 X1 (σ X0)
       grind)
    | exact resolve eq28 eq869520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq869520
  have eq874711 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq873833 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq873833
    | (have j0 := eq873833 X0 X1
       grind)
    | exact resolve eq873833 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873833
  have eq875126 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq874711 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq874711
    | (have j0 := eq874711 X0 X1
       grind)
    | exact resolve eq874711 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874711
  have eq875188 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq875126 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq875126
    | (have j0 := eq875126 X0 X1
       grind)
    | exact resolve eq875126 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875126
  have eq878658 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq875188 X0 X1
       grind)
    | exact superpose eq875188 eq11
    | (have j1 := eq875188 X0 X1
       grind)
    | exact resolve eq11 eq875188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875188
  have eq880292 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq878658 y x
       grind)
    | exact superpose eq878658 eq16
    | (have j1 := eq878658 y x
       grind)
    | exact resolve eq16 eq878658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878658
  have eq880851 : y = (k y x) := by
    first
    | (have j1 := eq872228 x y
       grind)
    | (have r₁ := eq880292
       have r₂ := eq872228 x y
       grind)
    | exact resolve eq880292 eq872228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872228 eq880292
  have eq881145 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq3739 x y
       have i₂ := eq880851
       grind)
    | exact superpose eq880851 eq3739
    | (have j0 := eq3739 x y
       grind)
    | exact resolve eq3739 eq880851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3739
  have eq881174 : y ≠ y ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq28146 y x
       have i₂ := eq880851
       grind)
    | exact superpose eq880851 eq28146
    | (have j0 := eq28146 y x
       grind)
    | (have r₁ := eq28146 y x
       have r₂ := eq880851
       grind)
    | exact resolve eq28146 eq880851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28146
  have eq881221 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq881174
  have eq881222 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq881145
  have eq881236 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq881221
       grind)
    | exact superpose eq881221 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq881221
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq881221
       grind)
    | exact resolve eq12 eq881221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881221
  have eq881274 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq881236
  have eq881276 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq881274
       have i₂ := eq880851
       grind)
    | exact superpose eq880851 eq881274
    | exact resolve eq881274 eq880851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881274
  have eq881277 : y = (M.op x y) := by grind
  clear eq881276
  have eq988607 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq881222
       grind)
    | exact superpose eq881222 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq881222
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq881222
       grind)
    | exact resolve eq12 eq881222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881222
  have eq988646 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq988607
  have eq988663 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq988646
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq988646
    | exact resolve eq988646 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988646
  have eq988686 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq988663
       have i₂ := eq880851
       grind)
    | exact superpose eq880851 eq988663
    | exact resolve eq988663 eq880851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880851 eq988663
  have eq988687 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq988686
  have eq988695 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq988687
       grind)
    | exact superpose eq988687 eq16
    | exact resolve eq16 eq988687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988687
  have eq988871 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq988695
       have i₂ := eq881277
       grind)
    | exact superpose eq881277 eq988695
    | exact resolve eq988695 eq881277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881277 eq988695
  have eq988872 : False := by grind
  exact eq988872

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyx_pyx_pxx_pyx_Equation2300 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq83 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq123 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq83 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq83 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq83 X0 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq83 X0 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq126 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq123 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq127 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq126 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq129 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq127 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq127
    | (have j0 := eq127 X0 X1
       grind)
    | exact resolve eq127 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq133 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq129 X0 X1
       have j1 := eq125 X1 X0
       grind)
    | (have r₁ := eq129 X1 X0
       have r₂ := eq125 X0 X1
       grind)
    | (have r₁ := eq129 (k X1 X0) X1
       have r₂ := eq125 X0 X1
       grind)
    | (have r₁ := eq129 X1 X1
       have r₂ := eq125 X1 X1
       grind)
    | exact resolve eq129 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq129
  have eq514 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq133 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq133
    | exact resolve eq133 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq528 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq133 y x
       grind)
    | exact superpose eq133 eq16
    | (have j1 := eq133 y x
       grind)
    | exact resolve eq16 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq543 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq514 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq514
    | (have j0 := eq514 X0 X1
       grind)
    | exact resolve eq514 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq514
  have eq544 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq543 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq543
    | exact resolve eq543 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq603 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq544 (τ X1) X0
       grind)
    | exact superpose eq544 eq18
    | (have j1 := eq544 (τ X1) X0
       grind)
    | exact resolve eq18 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq544
  have eq806 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq603 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq603
    | exact resolve eq603 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq865 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq806 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq806
    | (have j0 := eq806 X0 X1
       grind)
    | exact resolve eq806 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq978 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq528
       have i₂ := eq865 y x
       grind)
    | exact superpose eq865 eq528
    | (have j1 := eq865 (σ y) (σ x)
       grind)
    | (have r₁ := eq528
       have r₂ := eq865 y x
       grind)
    | exact resolve eq528 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq979 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq978
  have eq987 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq979
  have eq1034 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq528
       have i₂ := eq987
       grind)
    | exact superpose eq987 eq528
    | exact resolve eq528 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528 eq987
  have eq1035 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1034
  have eq1036 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1035
  have eq1050 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1036
  have eq1058 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1050
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1050
    | exact resolve eq1050 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050
  have eq1095 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1058
       grind)
    | exact superpose eq1058 eq16
    | exact resolve eq16 eq1058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058
  have eq1104 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1095
       have i₂ := eq865 y x
       grind)
    | exact superpose eq865 eq1095
    | (have j1 := eq865 y x
       grind)
    | (have r₁ := eq1095
       have r₂ := eq865 y x
       grind)
    | exact resolve eq1095 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq1105 : y = (M.op x x) := by grind
  clear eq1104
  have eq1145 : (M.op x y) = (k y x) := by grind
  clear eq1105
  have eq1152 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1095
       have i₂ := eq1145
       grind)
    | exact superpose eq1145 eq1095
    | exact resolve eq1095 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095 eq1145
  have eq1155 : False := by grind
  exact eq1155

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation2300 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
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
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq114 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq116 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
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
  have eq585 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) X0
       have i₂ := eq116 X0 X1
       grind)
    | exact superpose eq116 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq116 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) X0
       have r₂ := eq116 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X1)
       have r₂ := eq116 (M.op (τ X1) X0) X1
       grind)
    | exact resolve eq13 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq596 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq585 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq597 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq596 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq783 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq2150 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq597 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq597
    | exact resolve eq597 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq2201 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2150 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2150
    | (have j0 := eq2150 X0 X1
       grind)
    | exact resolve eq2150 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2150
  have eq2243 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq2201 X1 X0
       grind)
    | exact superpose eq2201 eq10
    | (have j1 := eq2201 X1 X0
       grind)
    | exact resolve eq10 eq2201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2285 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2243 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq2243
    | (have j0 := eq2243 X0 X1
       grind)
    | exact resolve eq2243 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2243
  have eq2323 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0
       have i₂ := eq2285 X0 (σ X1)
       grind)
    | exact superpose eq2285 eq37
    | (have j1 := eq2285 X0 (σ X1)
       grind)
    | exact resolve eq37 eq2285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2285
  have eq4065 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X1) X0
       have i₂ := eq2323 (σ X0) X1
       grind)
    | exact superpose eq2323 eq28
    | (have j1 := eq2323 (σ X0) X1
       grind)
    | exact resolve eq28 eq2323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2323
  have eq4126 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4065 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4065
    | (have j0 := eq4065 X0 X1
       grind)
    | exact resolve eq4065 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4065
  have eq4160 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4126 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4126
    | (have j0 := eq4126 X0 X1
       grind)
    | exact resolve eq4126 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4126
  have eq4170 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4160 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4160
    | (have j0 := eq4160 X0 X1
       grind)
    | exact resolve eq4160 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4160
  have eq4371 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq4170 X1 X0
       grind)
    | exact superpose eq4170 eq11
    | (have j1 := eq4170 X1 X0
       grind)
    | exact resolve eq11 eq4170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4170
  have eq5235 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4371 y x
       grind)
    | exact superpose eq4371 eq16
    | (have j1 := eq4371 y x
       grind)
    | exact resolve eq16 eq4371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4371
  have eq5264 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5235
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq5235
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq5235
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5235
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5235 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5265 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq5235
       have i₂ := eq2201 y x
       grind)
    | exact superpose eq2201 eq5235
    | (have j1 := eq2201 y x
       grind)
    | (have r₁ := eq5235
       have r₂ := eq2201 y x
       grind)
    | (have r₁ := eq5235
       have r₂ := eq2201 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5235
       have r₂ := eq2201 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5235 eq2201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2201 eq5235
  have eq5268 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5265
  have eq5269 : x = y ∨ (σ x) = (σ y) ∨ x = (k y x) := by grind
  clear eq5268
  have eq5270 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5264
  have eq5271 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq5270
  have eq5275 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5269
       grind)
    | exact superpose eq5269 eq16
    | exact resolve eq16 eq5269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5269
  have eq5276 : x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5275
       have r₂ := eq22 x
       grind)
    | exact resolve eq5275 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5275
  have eq5282 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq783 x y
       have i₂ := eq5276
       grind)
    | exact superpose eq5276 eq783
    | (have j0 := eq783 x y
       grind)
    | exact resolve eq783 eq5276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783 eq5276
  have eq5287 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5282
  have eq5288 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5287
  have eq5292 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5271
       grind)
    | exact superpose eq5271 eq16
    | exact resolve eq16 eq5271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5271
  have eq5293 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5292
       have r₂ := eq22 x
       grind)
    | exact resolve eq5292 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5292
  have eq5303 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5288
       grind)
    | exact superpose eq5288 eq16
    | exact resolve eq16 eq5288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5288
  have eq5326 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5303
       have i₂ := eq5293
       grind)
    | exact superpose eq5293 eq5303
    | exact resolve eq5303 eq5293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5293 eq5303
  have eq5327 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq5326
  have eq5328 : (σ x) = (σ y) := by grind
  clear eq5327
  have eq5329 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5328
       grind)
    | exact superpose eq5328 eq16
    | exact resolve eq16 eq5328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5330 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5328
       grind)
    | exact superpose eq5328 eq10
    | exact resolve eq10 eq5328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5328
  have eq5382 : x = y := by
    first
    | (have i₁ := eq5330
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5330
    | exact resolve eq5330 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5330
  have eq5383 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5329
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5329
    | exact resolve eq5329 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5329
  have eq5384 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5383
       have i₂ := eq5382
       grind)
    | exact superpose eq5382 eq5383
    | exact resolve eq5383 eq5382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5382 eq5383
  have eq5385 : False := by grind
  exact eq5385

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_y_pxy_Equation2373 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2373 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  have eq54 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq14 X0 X2 X3
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
  clear eq52
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
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
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq78
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq78
    | exact resolve eq78 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq85 : (M.op y x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq84
    | exact resolve eq84 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq218 : ∀ X0 X1 : G, (M.op X1 (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op X0 (M.op X1 (σ x))) X0) := by
    intro X0 X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq699 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0)) X3) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3 (M.op X1 X2)
       have i₂ := eq55 X1 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq8070 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op (M.op X0 X1) X0)) (M.op (σ y) (M.op (σ x) (σ y)))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq218 eq699
    | exact resolve eq699 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq699
  have eq131508 : y = (M.op (M.op (σ x) (M.op (M.op y x) y)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq8070 y y
       have i₂ := eq85
       grind)
    | exact superpose eq85 eq8070
    | exact resolve eq8070 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq131523 : x = y ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq8070 eq131508
    | exact resolve eq131508 eq8070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131508
  have eq131524 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by grind
  clear eq131523
  have eq131594 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq131524 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq131524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131524
  have eq131601 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq131594
    | exact resolve eq131594 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131594
  have eq131612 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq131601
       have r₂ := eq28
       grind)
    | exact resolve eq131601 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131601
  have eq131746 : (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ y) (σ x)) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq131612 eq8070
    | exact resolve eq8070 eq131612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131612
  have eq131762 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq8070 eq131746
    | exact resolve eq131746 eq8070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8070 eq131746
  have eq131763 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq131762
  have eq131812 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq131763 eq30
    | exact resolve eq30 eq131763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq131763
  have eq132037 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq131812
    | exact resolve eq131812 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq131812
  have eq132038 : x = y := by grind
  clear eq132037
  have eq132347 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq132038
       grind)
    | exact superpose eq132038 eq19
    | exact resolve eq19 eq132038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq132348 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq132038
       grind)
    | exact superpose eq132038 eq25
    | exact resolve eq25 eq132038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq132038
  have eq132570 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq132348
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq132348
    | exact resolve eq132348 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq132348
  have eq132600 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq132570 eq27
    | exact resolve eq27 eq132570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq132570
  have eq133910 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq132600 eq68
    | exact resolve eq68 eq132600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq132600
  have eq134171 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq133910
       have i₂ := eq132347
       grind)
    | exact superpose eq132347 eq133910
    | exact resolve eq133910 eq132347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132347 eq133910
  have eq134264 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq134171 eq15
    | exact resolve eq15 eq134171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134171
  have eq134344 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq134264
    | exact resolve eq134264 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq134264
  have eq134365 : False := by grind
  exact eq134365

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pyx_pxy_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq72 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq72
    | (have j0 := eq72 (σ X0) (σ X1)
       grind)
    | exact resolve eq72 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq72 y x
       grind)
    | exact superpose eq72 eq69
    | (have j1 := eq72 y x
       grind)
    | exact resolve eq69 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
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
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq105
    | exact resolve eq105 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq126 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq201 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq204 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq201 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq201
    | (have j0 := eq201 X0
       grind)
    | exact resolve eq201 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq514 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq52 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x X0 X1 y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq518 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq521 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq518 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq518
    | exact resolve eq518 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq530 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq521 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq521
    | (have j0 := eq521 x y
       grind)
    | exact resolve eq521 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : ∀ X0 : G, (M.op x y) = (M.op (M.op x (M.op (M.op x y) X0)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq530 eq14
    | exact resolve eq14 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq664 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq88 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq683 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq106 eq72
    | (have j0 := eq72 (σ y) (σ x)
       grind)
    | exact resolve eq72 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq684 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq683
    | exact resolve eq683 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq687 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq684
       have r₂ := eq27
       grind)
    | exact resolve eq684 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq689 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq687 eq521
    | exact resolve eq521 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq687 eq14
    | exact resolve eq14 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (σ x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq693 X0
       have i₂ := eq521 sF3 (M.op sF3 X0)
       grind)
    | (have i₁ := eq693 x
       have i₂ := eq521 sF3 x
       grind)
    | exact superpose eq521 eq693
    | exact resolve eq693 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq708 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq689 eq695
    | exact resolve eq695 eq689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq717 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq708
  have eq756 : (σ x) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq717 eq687
    | exact resolve eq687 eq717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq757 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq717 eq695
    | exact resolve eq695 eq717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695 eq717
  have eq764 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq757
  have eq765 : y = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq756
  have eq768 : y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq521 y x
       have i₂ := eq765
       grind)
    | exact superpose eq765 eq521
    | exact resolve eq521 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq772 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq765
       grind)
    | exact superpose eq765 eq14
    | exact resolve eq14 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq774 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq772 X0
       have i₂ := eq521 y X0
       grind)
    | (have i₁ := eq772 X0
       have i₂ := eq521 y (M.op y X0)
       grind)
    | exact superpose eq521 eq772
    | exact resolve eq772 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521 eq772
  have eq839 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq774 y
       have i₂ := eq768
       grind)
    | exact superpose eq768 eq774
    | exact resolve eq774 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768 eq774
  have eq850 : x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq839
  have eq853 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq765
       have i₂ := eq850
       grind)
    | exact superpose eq850 eq765
    | exact resolve eq765 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765 eq850
  have eq863 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq853
  have eq866 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq863 eq29
    | exact resolve eq29 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq863
  have eq888 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq866
    | exact resolve eq866 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq866
  have eq889 : x = y := by grind
  clear eq888
  have eq890 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq889
       grind)
    | exact superpose eq889 eq18
    | exact resolve eq18 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq891 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq889
       grind)
    | exact superpose eq889 eq24
    | exact resolve eq24 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq914 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq891
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq891
    | exact resolve eq891 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891
  have eq915 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq914 eq26
    | exact resolve eq26 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq949 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq915 eq764
    | exact resolve eq764 eq915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq957 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq949
       have i₂ := eq889
       grind)
    | exact superpose eq889 eq949
    | exact resolve eq949 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq959 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq957
       have i₂ := eq890
       grind)
    | exact superpose eq890 eq957
    | exact resolve eq957 eq890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq965 : ∀ X0 : G, x = (M.op (M.op (M.op x (M.op (M.op x y) X0)) (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq514 x X0
       have i₂ := eq890
       grind)
    | exact superpose eq890 eq514
    | exact resolve eq514 eq890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq986 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq548 eq965
    | exact resolve eq965 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965
  have eq992 : (M.op x y) = (M.op (M.op x x) (M.op x y)) := by
    first
    | exact superpose eq986 eq548
    | exact resolve eq548 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548 eq986
  have eq1005 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq992
       have i₂ := eq890
       grind)
    | exact superpose eq890 eq992
    | exact resolve eq992 eq890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq1013 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq1005 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq1005
       grind)
    | exact resolve eq13 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1017 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1005 eq14
    | exact resolve eq14 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1018 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have j0 := eq1013 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq1019 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq204 eq1017
    | exact resolve eq1017 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq1017
  have eq1108 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq959 eq27
    | exact resolve eq27 eq959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959
  have eq1253 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq1018 eq126
    | exact resolve eq126 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq1018
  have eq1261 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1005 eq1253
    | exact resolve eq1253 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253
  have eq1264 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq1261
    | exact resolve eq1261 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261
  have eq1370 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1019 eq14
    | exact resolve eq14 eq1019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019
  have eq1377 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1005 eq1370
    | exact resolve eq1370 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005 eq1370
  have eq1398 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) X0) X1) X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1377 eq14
    | exact resolve eq14 eq1377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1408 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1377 eq1398
    | exact resolve eq1398 eq1377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377 eq1398
  have eq1679 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 X0
       have i₂ := eq1408 X0 X1
       grind)
    | exact superpose eq1408 eq14
    | exact resolve eq14 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1408
  have eq2052 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq1679 X0 (M.op X0 X0)
       grind)
    | exact superpose eq1679 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq1679 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq1679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2067 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2052 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2052
  have eq2078 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2067 X0 X1
       have i₂ := eq1679 X0 X1
       grind)
    | exact superpose eq1679 eq2067
    | exact resolve eq2067 eq1679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1679 eq2067
  have eq2275 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq764 eq2078
    | exact resolve eq2078 eq764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764 eq2078
  have eq2294 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2275 X0
       have i₂ := eq889
       grind)
    | exact superpose eq889 eq2275
    | (have j0 := eq2275 X0
       grind)
    | exact resolve eq2275 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2275
  have eq2306 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2294 X0
       have i₂ := eq890
       grind)
    | exact superpose eq890 eq2294
    | (have j0 := eq2294 X0
       grind)
    | exact resolve eq2294 eq890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2294
  have eq3811 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq664 x
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq664
    | (have j0 := eq664 x
       grind)
    | exact resolve eq664 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq664
  have eq3827 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3811
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3811
    | exact resolve eq3811 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3811
  have eq3843 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq3827
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3827
    | exact resolve eq3827 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3827
  have eq3849 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq915 eq3843
    | exact resolve eq3843 eq915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915 eq3843
  have eq4338 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2306 eq106
    | exact resolve eq106 eq2306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq2306
  have eq4362 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq914 eq4338
    | exact resolve eq4338 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914 eq4338
  have eq4371 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4362
       have r₂ := eq1108
       grind)
    | exact resolve eq4362 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108 eq4362
  have eq4374 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4371
       have i₂ := eq889
       grind)
    | exact superpose eq889 eq4371
    | exact resolve eq4371 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889 eq4371
  have eq4376 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4374
       have i₂ := eq890
       grind)
    | exact superpose eq890 eq4374
    | exact resolve eq4374 eq890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890 eq4374
  have eq4377 : x = (M.op x y) := by grind
  clear eq4376
  have eq4382 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq4377 eq20
    | exact resolve eq20 eq4377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4377
  have eq4428 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4382
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4382
    | exact resolve eq4382 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4382
  have eq4472 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4428 eq3849
    | exact resolve eq3849 eq4428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3849 eq4428
  have eq4474 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq4472
       have r₂ := eq1264
       grind)
    | exact resolve eq4472 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264 eq4472
  have eq4492 : False := by grind
  exact eq4492

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) X2) X1 X0
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
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq25
  have eq55 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq78 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq87 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq20 X0 X1 X2 X3
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq87 X0 x x X3 X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq87
    | exact resolve eq87 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq116 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq55 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq55
    | exact resolve eq55 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq127 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq116 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq116
    | (have j0 := eq116 X0
       grind)
    | exact resolve eq116 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq128 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq127 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq127
    | (have j0 := eq127 X0
       grind)
    | exact resolve eq127 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq129 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq128 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq128 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq128 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq132 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq129 (σ X0)
       grind)
    | exact superpose eq129 eq15
    | exact resolve eq15 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq129 (τ X0)
       grind)
    | exact superpose eq129 eq34
    | exact resolve eq34 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq141 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq134 X0
       have i₂ := eq129 X0
       grind)
    | exact superpose eq129 eq134
    | exact resolve eq134 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq143 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq132 X0
       have i₂ := eq129 X0
       grind)
    | exact superpose eq129 eq132
    | exact resolve eq132 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq132
  have eq164 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq143 X0
       grind)
    | exact superpose eq143 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (σ X2) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq78 X0 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq78
    | (have j0 := eq78 X2 X1
       grind)
    | exact resolve eq78 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq185 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (σ (M.op X2 X2)) ∨ (k X0 (σ X1)) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq170 X0 X1 X2
       have i₂ := eq143 X2
       grind)
    | exact superpose eq143 eq170
    | (have j0 := eq170 X0 X1 X2
       grind)
    | exact resolve eq170 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq380 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq20 X0 X0 x X0
       have i₂ := eq93 X0 X0 x
       grind)
    | exact superpose eq93 eq20
    | exact resolve eq20 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq428 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq93 X0 X0 X0
       have i₂ := eq380 X0
       grind)
    | exact superpose eq380 eq93
    | exact resolve eq93 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq380
  have eq513 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op X0 X0) X1
       have i₂ := eq428 X0
       grind)
    | exact superpose eq428 eq9
    | exact resolve eq9 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq514 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq428 X0
       grind)
    | exact superpose eq428 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq428 X0
       grind)
    | exact resolve eq12 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq514 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq525 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq513 X0 X1
       have i₂ := eq21 X0 X0 X1
       grind)
    | exact superpose eq21 eq513
    | exact resolve eq513 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq513
  have eq823 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq525 X0 X1
       grind)
    | exact superpose eq525 eq9
    | exact resolve eq9 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq832 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq823 X0 X1
       have i₂ := eq428 X0
       grind)
    | exact superpose eq428 eq823
    | exact resolve eq823 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428 eq823
  have eq952 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq832 (σ X0) X1
       have i₂ := eq143 X0
       grind)
    | exact superpose eq143 eq832
    | exact resolve eq832 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq954 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq832 (τ X0) X1
       have i₂ := eq141 X0
       grind)
    | exact superpose eq141 eq832
    | exact resolve eq832 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq832
  have eq1057 : ∀ X0 X1 : G, (M.op (σ (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq952 (σ (M.op X0 X0)) X1
       have i₂ := eq952 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq952 eq952
    | exact resolve eq952 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952
  have eq1314 : ∀ X0 X1 : G, (M.op (σ (σ (M.op X0 X0))) X1) = (k X1 (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq520 (σ (σ (M.op X0 X0))) X1
       have i₂ := eq1057 X0 (σ (σ (M.op X0 X0)))
       grind)
    | exact superpose eq1057 eq520
    | exact resolve eq520 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq1345 : ∀ X0 X1 : G, (k X1 (σ (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1314 X0 X1
       have i₂ := eq1057 X0 X1
       grind)
    | exact superpose eq1057 eq1314
    | exact resolve eq1314 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057 eq1314
  have eq1655 : ∀ X0 X1 : G, (k X1 (σ (σ (τ (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1345 (τ (M.op X0 X0)) X1
       have i₂ := eq954 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq954 eq1345
    | exact resolve eq1345 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq1699 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1655 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq1655
    | exact resolve eq1655 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1655
  have eq3480 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X2)) = (M.op (σ X2) (k X0 (σ (σ (M.op X1 X1))))) ∨ (σ X2) = (σ (M.op X2 X2)) ∨ (σ X2) = (k X0 (σ (σ (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq185 X0 (σ (M.op X1 X1)) X2
       have i₂ := eq1699 X1 (τ X0)
       grind)
    | exact superpose eq1699 eq185
    | (have j0 := eq185 X0 (σ (M.op X1 X1)) X2
       grind)
    | exact resolve eq185 eq1699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq1699
  have eq3555 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X2)) = (M.op (σ X2) X0) ∨ (σ X2) = (σ (M.op X2 X2)) ∨ (σ X2) = (k X0 (σ (σ (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3480 X0 X1 X2
       have i₂ := eq1345 X1 X0
       grind)
    | exact superpose eq1345 eq3480
    | (have j0 := eq3480 X0 X1 X2
       grind)
    | exact resolve eq3480 eq1345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3480
  have eq3576 : ∀ X0 X1 X2 : G, (k X0 (σ X2)) = (M.op (σ X2) X0) ∨ (σ X2) = (σ (M.op X2 X2)) ∨ (σ X2) = (k X0 (σ (σ (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3555 X0 X1 X2
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq3555
    | (have j0 := eq3555 X0 X1 X2
       grind)
    | exact resolve eq3555 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3555
  have eq3592 : ∀ X0 X1 X2 : G, (k X0 (σ X2)) = (M.op (σ X2) X0) ∨ (σ X2) = (k X0 (σ (σ (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3576 X0 X1 X2
       have j1 := eq164 X2 X0
       grind)
    | (have r₁ := eq3576 X0 X1 X0
       have r₂ := eq164 X0 X1
       grind)
    | exact resolve eq3576 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq3576
  have eq3605 : ∀ X0 X2 : G, (k X0 (σ X2)) = (M.op (σ X2) X0) ∨ (σ X2) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq3592 X0 x X2
       have i₂ := eq1345 x X0
       grind)
    | exact superpose eq1345 eq3592
    | (have j0 := eq3592 X0 x X2
       grind)
    | exact resolve eq3592 eq1345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1345 eq3592
  have eq7587 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3605 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3605
    | exact resolve eq3605 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7620 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq3605 (σ X1) X0
       grind)
    | exact superpose eq3605 eq15
    | (have j1 := eq3605 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq3605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3605
  have eq7676 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq7587 (τ X0) X1
       grind)
    | exact superpose eq7587 eq19
    | (have j1 := eq7587 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq7587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq7587
  have eq9994 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7676 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7676
    | exact resolve eq7676 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7676
  have eq10076 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9994 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq9994
    | (have j0 := eq9994 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq9994 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9994
  have eq17297 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7620 x y
       grind)
    | exact superpose eq7620 eq16
    | (have j1 := eq7620 x y
       grind)
    | exact resolve eq16 eq7620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7620
  have eq17722 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq17297
       have i₂ := eq10076 x y
       grind)
    | exact superpose eq10076 eq17297
    | (have j1 := eq10076 (σ x) (σ y)
       grind)
    | (have r₁ := eq17297
       have r₂ := eq10076 x y
       grind)
    | (have r₁ := eq17297
       have r₂ := eq10076 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq17297
       have r₂ := eq10076 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq17297 eq10076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10076 eq17297
  have eq17725 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq17722
  have eq17728 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17725
       grind)
    | exact superpose eq17725 eq16
    | exact resolve eq16 eq17725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17725
  have eq17729 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq17728
       have r₂ := eq143 x
       grind)
    | exact resolve eq17728 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17728
  have eq18145 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17729
       grind)
    | exact superpose eq17729 eq16
    | exact resolve eq16 eq17729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18146 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq17729
       grind)
    | exact superpose eq17729 eq10
    | exact resolve eq10 eq17729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17729
  have eq18217 : x = y := by
    first
    | (have i₁ := eq18146
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq18146
    | exact resolve eq18146 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18146
  have eq18218 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq18145
       have i₂ := eq143 x
       grind)
    | exact superpose eq143 eq18145
    | exact resolve eq18145 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq18145
  have eq18223 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq18218
       have i₂ := eq18217
       grind)
    | exact superpose eq18217 eq18218
    | exact resolve eq18218 eq18217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18217 eq18218
  have eq18224 : False := by grind
  exact eq18224

/-- `Equation2653`: `x = ((x ◇ x) ◇ (y ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pxy_pxx_pxy_Equation2653 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2653 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2653.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X1) = X0 := by
    intro X0 X1
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq19 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq9 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq28 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
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
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq64 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq19 (M.op X0 X0)
       have i₂ := eq19 X0
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq19 X0
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X0)) (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0)
       have i₂ := eq19 X0
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X1
       have i₂ := eq19 X0
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq93 : ∀ X0 X1 X2 : G, (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (σ X0)) ∨ (k X1 (σ X2)) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) (k X1 (σ X2))
       have i₂ := eq21 X1 X2 X0
       grind)
    | exact superpose eq21 eq14
    | (have j0 := eq14 (σ X0) (k X1 (σ X2))
       grind)
    | exact resolve eq14 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 (k X1 (τ X0)) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq72
    | exact resolve eq72 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (k X0 X0)) (M.op X1 X1)) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq72 X0 X0
       grind)
    | exact superpose eq72 eq9
    | (have j1 := eq72 X0 X0
       grind)
    | exact resolve eq9 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq115 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (k X0 X0)) (M.op X1 X1)) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq108 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq219 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq67 (M.op (M.op X0 X0) X0) X0
       have i₂ := eq66 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq66 eq67
    | exact resolve eq67 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq220 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq67 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq67
    | exact resolve eq67 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq220 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq220
    | exact resolve eq220 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq227 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq219 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq219
    | exact resolve eq219 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq228 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq226 X0
       have i₂ := eq19 (M.op X0 X0)
       grind)
    | exact superpose eq19 eq226
    | exact resolve eq226 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq229 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq228 X0
       have i₂ := eq19 X0
       grind)
    | exact superpose eq19 eq228
    | exact resolve eq228 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq230 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq229 (M.op X0 X0)
       have i₂ := eq19 X0
       grind)
    | exact superpose eq19 eq229
    | exact resolve eq229 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq236 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq230 X0
       have i₂ := eq229 X0
       grind)
    | exact superpose eq229 eq230
    | exact resolve eq230 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq311 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq227 X0
       grind)
    | exact superpose eq227 eq9
    | exact resolve eq9 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq312 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq227 X0
       grind)
    | exact superpose eq227 eq9
    | exact resolve eq9 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) X1) = (M.op (M.op X0 (M.op X2 X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq311 X0 X2
       have i₂ := eq311 X0 X1
       grind)
    | exact superpose eq311 eq311
    | exact resolve eq311 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq340 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X1) = (M.op (M.op X1 X0) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq311 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq227 X0
       grind)
    | exact superpose eq227 eq311
    | exact resolve eq311 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0
       have i₂ := eq311 X0 X1
       grind)
    | exact superpose eq311 eq65
    | exact resolve eq65 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq353 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op X1 X1)) X1) (M.op X2 X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X0 X2
       have i₂ := eq311 X0 X1
       grind)
    | exact superpose eq311 eq67
    | exact resolve eq67 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq354 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X1) (M.op (M.op X0 (M.op X1 X1)) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq227 X0
       have i₂ := eq311 X0 X1
       grind)
    | exact superpose eq311 eq227
    | exact resolve eq227 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq229 X0
       have i₂ := eq311 X0 X1
       grind)
    | exact superpose eq311 eq229
    | exact resolve eq229 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 (M.op X1 X1)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq236 X0
       have i₂ := eq311 X0 X1
       grind)
    | exact superpose eq311 eq236
    | exact resolve eq236 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op (k (σ (τ X0)) X0) (M.op X1 X1)) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq115 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq115
    | (have j0 := eq115 (τ X0) X1
       grind)
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq399 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) (M.op X1 X1)) X1) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq387 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq387
    | (have j0 := eq387 X0 X1
       grind)
    | exact resolve eq387 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq402 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) (M.op X1 X1)) X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq399 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq399
    | (have j0 := eq399 X0 X1
       grind)
    | exact resolve eq399 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq406 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq351 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq227 X0
       grind)
    | exact superpose eq227 eq351
    | exact resolve eq351 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq420 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq351 (M.op X0 X0) x
       have i₂ := eq9 X0 x
       grind)
    | exact superpose eq9 eq351
    | exact resolve eq351 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X0 (M.op X1 X1)) X1) (M.op (M.op X0 (M.op X1 X1)) X1)) = (k (M.op (M.op X0 (M.op X1 X1)) X1) X0) ∨ (M.op X0 (M.op (M.op X0 (M.op X1 X1)) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op (M.op X0 (M.op X1 X1)) X1) X0
       have i₂ := eq351 X0 X1
       grind)
    | exact superpose eq351 eq13
    | (have j0 := eq13 (M.op (M.op X0 (M.op X1 X1)) X1) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op X0 (M.op X1 X1)) X1) X0
       have r₂ := eq351 X0 X1
       grind)
    | exact resolve eq13 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X1) (M.op (M.op X0 (M.op X1 X1)) X1)) = (k (M.op (M.op X0 (M.op X1 X1)) X1) X0) ∨ (M.op X0 (M.op (M.op X0 (M.op X1 X1)) X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq425 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq430 : ∀ X0 X1 : G, (k (M.op (M.op X0 (M.op X1 X1)) X1) X0) = X0 ∨ (M.op X0 (M.op (M.op X0 (M.op X1 X1)) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq427 X0 X1
       have i₂ := eq354 X0 X1
       grind)
    | exact superpose eq354 eq427
    | (have j0 := eq427 X0 X1
       grind)
    | exact resolve eq427 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq441 : ∀ X0 X1 : G, (k (M.op (M.op X0 (M.op X1 X1)) X1) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq430 X0 X1
       have i₂ := eq356 X0 X1
       grind)
    | exact superpose eq356 eq430
    | (have j0 := eq430 X0 X1
       grind)
    | exact resolve eq430 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq510 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X2) X0) (M.op (M.op X0 (M.op X1 X1)) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq312 X0 X2
       have i₂ := eq311 X0 X1
       grind)
    | exact superpose eq311 eq312
    | exact resolve eq312 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X0 X0) X0)) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq355 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq312 X0 X0
       grind)
    | exact superpose eq312 eq355
    | exact resolve eq355 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq648 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq356 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq312 X0 X0
       grind)
    | exact superpose eq312 eq356
    | exact resolve eq356 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq670 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op (M.op (M.op X0 (M.op X1 X1)) X1) X0) = (k (M.op (M.op X0 (M.op X1 X1)) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op (M.op X0 (M.op X1 X1)) X1) X0
       have i₂ := eq356 X0 X1
       grind)
    | exact superpose eq356 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : ∀ X0 X1 : G, (k (M.op (M.op X0 (M.op X1 X1)) X1) X0) = X0 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq670 X0 X1
       have i₂ := eq351 X0 X1
       grind)
    | exact superpose eq351 eq670
    | (have j0 := eq670 X0 X1
       grind)
    | exact resolve eq670 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq688 : ∀ X0 X1 : G, (k (M.op (M.op X0 (M.op X1 X1)) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq674 X0 X1
       have j1 := eq441 X0 X1
       grind)
    | (have r₁ := eq674 X0 X1
       have r₂ := eq441 X0 X1
       grind)
    | exact resolve eq674 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441 eq674
  have eq721 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op (M.op (σ X0) (M.op X1 X1)) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (M.op (M.op (σ X0) (M.op X1 X1)) X1) X0
       have i₂ := eq688 (σ X0) X1
       grind)
    | exact superpose eq688 eq23
    | exact resolve eq23 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq722 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op (M.op (τ X0) (M.op X1 X1)) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op (M.op (τ X0) (M.op X1 X1)) X1)
       have i₂ := eq688 (τ X0) X1
       grind)
    | exact superpose eq688 eq18
    | exact resolve eq18 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq726 : ∀ X0 X1 : G, (k (σ (M.op (M.op (τ X0) (M.op X1 X1)) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq722 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq722
    | exact resolve eq722 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq727 : ∀ X0 X1 : G, (k (τ (M.op (M.op (σ X0) (M.op X1 X1)) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq721 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq721
    | exact resolve eq721 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq871 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X0) (M.op (M.op X0 (M.op X1 X1)) X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq406 X0 X2
       have i₂ := eq311 X0 X1
       grind)
    | exact superpose eq311 eq406
    | exact resolve eq406 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq1080 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (σ (M.op (M.op (τ (τ X0)) (M.op X1 X1)) X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (σ (M.op (M.op (τ (τ X0)) (M.op X1 X1)) X1))
       have i₂ := eq726 (τ X0) X1
       grind)
    | exact superpose eq726 eq18
    | exact resolve eq18 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq1085 : ∀ X0 X1 : G, (k (σ (σ (M.op (M.op (τ (τ X0)) (M.op X1 X1)) X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1080 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1080
    | exact resolve eq1080 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080
  have eq1133 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (τ (M.op (M.op (σ (σ X0)) (M.op X1 X1)) X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (τ (M.op (M.op (σ (σ X0)) (M.op X1 X1)) X1)) X0
       have i₂ := eq727 (σ X0) X1
       grind)
    | exact superpose eq727 eq23
    | exact resolve eq23 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq1140 : ∀ X0 X1 : G, (k (τ (τ (M.op (M.op (σ (σ X0)) (M.op X1 X1)) X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1133 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1133
    | exact resolve eq1133 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133
  have eq1816 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k (k (σ X1) X2) (σ X0)) = (M.op (k (σ X1) X2) (k (σ X1) X2)) ∨ (σ X0) = (M.op (σ X0) (k (σ X1) X2)) ∨ (M.op (k (σ X1) X2) (σ X0)) = (σ (k (k X1 (τ X2)) X0)) ∨ (σ X0) = (M.op (σ X0) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k (σ X1) X2) (σ X0)
       have i₂ := eq100 X1 X2 X0
       grind)
    | exact superpose eq100 eq13
    | (have j0 := eq13 (k (σ X1) X2) (σ X0)
       have j1 := eq100 X1 X2 X0
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (σ X2)
       have r₂ := eq100 X0 X1 X2
       grind)
    | exact resolve eq13 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq1818 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k (k (σ X1) X2) (σ X0)) = (M.op (k (σ X1) X2) (k (σ X1) X2)) ∨ (σ X0) = (M.op (σ X0) (k (σ X1) X2)) ∨ (M.op (k (σ X1) X2) (σ X0)) = (σ (k (k X1 (τ X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1816 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1816
  have eq1819 : ∀ X0 X1 X2 : G, (k (k (σ X1) X2) (σ X0)) = (M.op (k (σ X1) X2) (k (σ X1) X2)) ∨ (σ X0) = (M.op (σ X0) (k (σ X1) X2)) ∨ (M.op (k (σ X1) X2) (σ X0)) = (σ (k (k X1 (τ X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1818 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1818
  have eq1821 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ (k (k X1 (τ X2)) X0)) = (M.op (k (σ X1) X2) (k (σ X1) X2)) ∨ (M.op (k (σ X1) X2) (σ X0)) = (σ (k (k X1 (τ X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1819 X0 X1 X2
       have i₂ := eq28 X1 X2 X0
       grind)
    | exact superpose eq28 eq1819
    | (have j0 := eq1819 X0 X1 X2
       grind)
    | exact resolve eq1819 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1819
  have eq2049 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op (M.op X1 X1) X1) (M.op (M.op X1 X1) X1)) (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq340 (M.op (M.op X1 X1) X1) (M.op X0 X1)
       have i₂ := eq340 X1 X0
       grind)
    | exact superpose eq340 eq340
    | exact resolve eq340 eq340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq2127 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op (M.op X1 X1) X1) (M.op X1 X1)) (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2049 X0 X1
       have i₂ := eq64 X1
       grind)
    | exact superpose eq64 eq2049
    | exact resolve eq2049 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq2049
  have eq2153 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op (M.op X0 X0) X0) (M.op X1 (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2127 X0 X1
       have i₂ := eq229 X1
       grind)
    | exact superpose eq229 eq2127
    | exact resolve eq2127 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2127
  have eq2167 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X1 X1)) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2153 X0 X1
       have i₂ := eq236 X1
       grind)
    | exact superpose eq236 eq2153
    | exact resolve eq2153 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2153
  have eq2245 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X1) (M.op (M.op X0 (M.op X2 X2)) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq510 X0 X2 X0
       have i₂ := eq311 X0 X1
       grind)
    | exact superpose eq311 eq510
    | exact resolve eq510 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq2687 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1))) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X0 (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq648 X1 (M.op (M.op X0 X0) (M.op X1 X1))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq648
    | exact resolve eq648 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq3604 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq351 (k X0 X0) x
       have i₂ := eq402 X0 x
       grind)
    | exact superpose eq402 eq351
    | (have j1 := eq402 X0 x
       grind)
    | exact resolve eq351 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq3657 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) (M.op (M.op (k X0 X0) (M.op X1 X1)) X1)) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq871 (k X0 X0) X1 X0
       have i₂ := eq3604 X0
       grind)
    | exact superpose eq3604 eq871
    | (have j1 := eq3604 X0
       grind)
    | exact resolve eq871 eq3604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871 eq3604
  have eq3666 : ∀ X0 : G, (M.op (M.op (k X0 X0) (k X0 X0)) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3657 X0 x
       have i₂ := eq356 (k X0 X0) x
       grind)
    | exact superpose eq356 eq3657
    | (have j0 := eq3657 X0 x
       grind)
    | exact resolve eq3657 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356 eq3657
  have eq4150 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (σ (σ (M.op (M.op (τ (τ (τ X0))) (M.op X1 X1)) X1)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (σ (σ (M.op (M.op (τ (τ (τ X0))) (M.op X1 X1)) X1)))
       have i₂ := eq1085 (τ X0) X1
       grind)
    | exact superpose eq1085 eq18
    | exact resolve eq18 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4161 : ∀ X0 X1 : G, (k (σ (σ (σ (M.op (M.op (τ (τ (τ X0))) (M.op X1 X1)) X1)))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4150 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4150
    | exact resolve eq4150 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4150
  have eq4232 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (τ (τ (M.op (M.op (σ (σ (σ X0))) (M.op X1 X1)) X1)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (τ (τ (M.op (M.op (σ (σ (σ X0))) (M.op X1 X1)) X1))) X0
       have i₂ := eq1140 (σ X0) X1
       grind)
    | exact superpose eq1140 eq23
    | exact resolve eq23 eq1140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq4245 : ∀ X0 X1 : G, (k (τ (τ (τ (M.op (M.op (σ (σ (σ X0))) (M.op X1 X1)) X1)))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4232 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4232
    | exact resolve eq4232 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4232
  have eq4886 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq312 X0 (k X0 X0)
       have i₂ := eq3666 X0
       grind)
    | exact superpose eq3666 eq312
    | (have j1 := eq3666 X0
       grind)
    | exact resolve eq312 eq3666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3666
  have eq4940 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4886 X0
       have i₂ := eq236 X0
       grind)
    | exact superpose eq236 eq4886
    | (have j0 := eq4886 X0
       grind)
    | exact resolve eq4886 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4886
  have eq4953 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4940 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq4940 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq4940 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4940
  have eq5227 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4953 (σ X0)
       grind)
    | exact superpose eq4953 eq15
    | exact resolve eq15 eq4953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5236 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq4953 (τ X0)
       grind)
    | exact superpose eq4953 eq33
    | exact resolve eq33 eq4953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq5251 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5236 X0
       have i₂ := eq4953 X0
       grind)
    | exact superpose eq4953 eq5236
    | exact resolve eq5236 eq4953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5236
  have eq5259 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5227 X0
       have i₂ := eq4953 X0
       grind)
    | exact superpose eq4953 eq5227
    | exact resolve eq5227 eq4953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4953 eq5227
  have eq5328 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ (M.op X0 X0)) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1
       have i₂ := eq5251 X0
       grind)
    | exact superpose eq5251 eq9
    | exact resolve eq9 eq5251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5367 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (τ (M.op X0 X0))) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq351 X1 (τ X0)
       have i₂ := eq5251 X0
       grind)
    | exact superpose eq5251 eq351
    | exact resolve eq351 eq5251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5611 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq420 (σ X0)
       have i₂ := eq5259 X0
       grind)
    | exact superpose eq5259 eq420
    | exact resolve eq420 eq5259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6353 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5611 (M.op (M.op X0 X0) X0)
       have i₂ := eq312 X0 X0
       grind)
    | exact superpose eq312 eq5611
    | exact resolve eq5611 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6783 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op (M.op X0 (M.op X1 X1)) X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6353 X0
       have i₂ := eq311 X0 X1
       grind)
    | exact superpose eq311 eq6353
    | exact resolve eq6353 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6353
  have eq7219 : ∀ X0 X1 : G, (M.op (M.op (τ X0) (M.op X1 X1)) X1) = (τ (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5328 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq312 X0 X0
       grind)
    | exact superpose eq312 eq5328
    | exact resolve eq5328 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312 eq5328
  have eq14779 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op (τ X0) (M.op X1 X1)) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6783 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6783
    | exact resolve eq6783 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6783
  have eq15151 : ∀ X0 X1 : G, (σ (M.op (M.op (τ X0) (M.op X1 X1)) X1)) = (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op (σ (M.op (M.op (τ X0) (M.op X1 X1)) X1)) (σ (M.op (M.op (τ X0) (M.op X1 X1)) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq562 X0 (σ (M.op (M.op (τ X0) (M.op X1 X1)) X1))
       have i₂ := eq14779 X0 X1
       grind)
    | exact superpose eq14779 eq562
    | exact resolve eq562 eq14779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562 eq14779
  have eq15204 : ∀ X0 X1 : G, (σ (M.op (M.op (τ X0) (M.op X1 X1)) X1)) = (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (σ (M.op (M.op (M.op (τ X0) (M.op X1 X1)) X1) (M.op (M.op (τ X0) (M.op X1 X1)) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq15151 X0 X1
       have i₂ := eq5259 (M.op (M.op (τ X0) (M.op X1 X1)) X1)
       grind)
    | exact superpose eq5259 eq15151
    | exact resolve eq15151 eq5259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15151
  have eq15244 : ∀ X0 X1 : G, (σ (M.op (M.op (τ X0) (M.op X1 X1)) X1)) = (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15204 X0 X1
       have i₂ := eq354 (τ X0) X1
       grind)
    | exact superpose eq354 eq15204
    | exact resolve eq15204 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15204
  have eq15257 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X0)) X0) = (σ (M.op (M.op (τ X0) (M.op X1 X1)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15244 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15244
    | exact resolve eq15244 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15244
  have eq15268 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (σ (M.op (M.op (τ X0) (M.op X1 X1)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15257 X0 X1
       have i₂ := eq236 X0
       grind)
    | exact superpose eq236 eq15257
    | exact resolve eq15257 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15257
  have eq35128 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X2)) X2) = (σ (M.op (M.op (τ X0) (M.op X1 X1)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq311 X0 X2
       have i₂ := eq15268 X0 X1
       grind)
    | exact superpose eq15268 eq311
    | exact resolve eq311 eq15268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15268
  have eq73596 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 X1)))) (M.op X2 X2)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq353 X0 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       have i₂ := eq339 (M.op X0 (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 X1)))) (M.op X1 X1) X2
       grind)
    | (have i₁ := eq353 X0 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       have i₂ := eq339 (M.op X0 (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 X1)))) X2 (M.op X1 X1)
       grind)
    | exact superpose eq339 eq353
    | exact resolve eq353 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339 eq353
  have eq74414 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op X1 (M.op (M.op X1 X1) X1)))) (M.op X2 X2)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq73596 X0 X1 X2
       have i₂ := eq2687 X1 X1
       grind)
    | exact superpose eq2687 eq73596
    | exact resolve eq73596 eq2687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2687 eq73596
  have eq74685 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op X1 X1))) (M.op X2 X2)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74414 X0 X1 X2
       have i₂ := eq236 X1
       grind)
    | exact superpose eq236 eq74414
    | exact resolve eq74414 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq74414
  have eq74783 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X1 X1) X1) (M.op X1 X1))) (M.op X2 X2)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74685 X0 X1 X2
       have i₂ := eq2167 X1 X1
       grind)
    | exact superpose eq2167 eq74685
    | exact resolve eq74685 eq2167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2167 eq74685
  have eq74825 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74783 X0 X1 X2
       have i₂ := eq229 X1
       grind)
    | exact superpose eq229 eq74783
    | exact resolve eq74783 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229 eq74783
  have eq76397 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op (M.op (M.op X1 X2) (τ (M.op X0 X0))) (τ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74825 X1 X2 (τ X0)
       have i₂ := eq5251 X0
       grind)
    | exact superpose eq5251 eq74825
    | exact resolve eq74825 eq5251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5251
  have eq76891 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op (M.op (M.op (M.op (σ X0) X1) (M.op X2 X2)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5259 X0
       have i₂ := eq74825 (σ X0) X1 X2
       grind)
    | exact superpose eq74825 eq5259
    | exact resolve eq5259 eq74825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5259 eq74825
  have eq151186 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k (σ X2) (k X0 (σ X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (σ X2) (k X0 (σ X1))
       have i₂ := eq93 X2 X0 X1
       grind)
    | exact superpose eq93 eq12
    | (have j0 := eq12 (σ X2) (k X0 (σ X1))
       have j1 := eq93 X2 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (k X1 (σ X2))
       have r₂ := eq93 X0 X1 X2
       grind)
    | exact resolve eq12 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq151220 : ∀ X0 X1 X2 : G, (k (σ X2) (k X0 (σ X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq151186 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151186
  have eq151242 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq151220 X0 X1 X2
       have i₂ := eq21 X0 X1 X2
       grind)
    | exact superpose eq21 eq151220
    | (have j0 := eq151220 X0 X1 X2
       grind)
    | exact resolve eq151220 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq151220
  have eq151243 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq151242 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151242
  have eq153112 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (τ (τ (τ (M.op (M.op (σ (σ (σ (σ X0)))) (M.op X1 X1)) X1))))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (τ (τ (τ (M.op (M.op (σ (σ (σ (σ X0)))) (M.op X1 X1)) X1)))) X0
       have i₂ := eq4245 (σ X0) X1
       grind)
    | exact superpose eq4245 eq23
    | exact resolve eq23 eq4245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq153197 : ∀ X0 X1 : G, (k (τ (τ (τ (τ (M.op (M.op (σ (σ (σ (σ X0)))) (M.op X1 X1)) X1))))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq153112 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq153112
    | exact resolve eq153112 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153112
  have eq165470 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ (k (k (σ (σ (M.op (M.op (τ (τ (τ X0))) (M.op X2 X2)) X2))) (τ X0)) X1)) ∨ (M.op X0 (σ X1)) = (σ (k (k (σ (σ (M.op (M.op (τ (τ (τ X0))) (M.op X2 X2)) X2))) (τ X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1821 X0 (σ (σ (M.op (M.op (τ (τ (τ X0))) (M.op X1 X1)) X1))) X0
       have i₂ := eq4161 X0 X1
       grind)
    | exact superpose eq4161 eq1821
    | exact resolve eq1821 eq4161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1821 eq4161
  have eq165601 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (k (τ X0) X1)) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (σ (k (k (σ (σ (M.op (M.op (τ (τ (τ X0))) (M.op X2 X2)) X2))) (τ X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq165470 X0 X1 X2
       have i₂ := eq1085 (τ X0) X2
       grind)
    | exact superpose eq1085 eq165470
    | (have j0 := eq165470 X0 X1 X2
       grind)
    | exact resolve eq165470 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165470
  have eq165691 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (σ (k (k (σ (σ (M.op (M.op (τ (τ (τ X0))) (M.op X2 X2)) X2))) (τ X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq165601 X0 X1 X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq165601
    | (have j0 := eq165601 X0 X1 X2
       grind)
    | exact resolve eq165601 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165601
  have eq165770 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq165691 X0 X1 x
       have i₂ := eq1085 (τ X0) x
       grind)
    | exact superpose eq1085 eq165691
    | (have j0 := eq165691 X0 X1 x
       grind)
    | exact resolve eq165691 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085 eq165691
  have eq165839 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq165770 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq165770
    | (have j0 := eq165770 X0 X1
       grind)
    | exact resolve eq165770 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165770
  have eq165875 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq165839 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq165839 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq165839 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165839
  have eq165992 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq165875 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq165875
    | exact resolve eq165875 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165875
  have eq166827 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq165992 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165992
  have eq167760 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X1) (M.op (M.op X0 (M.op X1 X1)) X1)) ≠ X0 ∨ (M.op (M.op (M.op X0 (M.op X1 X1)) X1) (M.op (M.op X0 (M.op X1 X1)) X1)) = (k (M.op (M.op X0 (M.op X1 X1)) X1) (M.op (M.op X0 (M.op X2 X2)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq166827 (M.op (M.op X0 (M.op X1 X1)) X1) (M.op (M.op X0 (M.op X2 X2)) X2)
       have i₂ := eq2245 X0 X1 X2
       grind)
    | exact superpose eq2245 eq166827
    | (have j0 := eq166827 (M.op (M.op X0 (M.op X1 X1)) X1) (M.op (M.op X0 (M.op X2 X2)) X2)
       grind)
    | exact resolve eq166827 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2245 eq166827
  have eq167869 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X1) (M.op (M.op X0 (M.op X1 X1)) X1)) = (k (M.op (M.op X0 (M.op X1 X1)) X1) (M.op (M.op X0 (M.op X2 X2)) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq167760 X0 X1 X2
       grind)
    | (have r₁ := eq167760 X0 X1 X2
       have r₂ := eq354 X0 X1
       grind)
    | exact resolve eq167760 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167760
  have eq167940 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 (M.op X1 X1)) X1) (M.op (M.op X0 (M.op X2 X2)) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq167869 X0 X1 X2
       have i₂ := eq354 X0 X1
       grind)
    | exact superpose eq354 eq167869
    | exact resolve eq167869 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq167869
  have eq194881 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (τ (M.op (M.op (M.op (M.op (σ X0) X1) (M.op X2 X2)) X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq76891 X0 X1 X2
       grind)
    | exact superpose eq76891 eq10
    | exact resolve eq10 eq76891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76891
  have eq329404 : ∀ X0 X2 : G, (k (M.op (M.op X0 X0) X0) (M.op (M.op X0 (M.op X2 X2)) X2)) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq167940 X0 x X2
       have i₂ := eq311 X0 x
       grind)
    | exact superpose eq311 eq167940
    | exact resolve eq167940 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq329456 : ∀ X0 X2 : G, (τ X0) = (k (τ (M.op (M.op X0 X0) X0)) (M.op (M.op (τ X0) (M.op X2 X2)) X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq167940 (τ X0) x X2
       have i₂ := eq7219 X0 x
       grind)
    | exact superpose eq7219 eq167940
    | exact resolve eq167940 eq7219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7219 eq167940
  have eq497204 : ∀ X0 X1 : G, (k (M.op (M.op X0 X0) X0) (σ (M.op (M.op (τ X0) (M.op X1 X1)) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq329404 X0 x
       have i₂ := eq35128 X0 X1 x
       grind)
    | exact superpose eq35128 eq329404
    | exact resolve eq329404 eq35128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35128 eq329404
  have eq866618 : ∀ X0 X1 X2 : G, (M.op (σ X2) X0) = X0 ∨ (M.op (σ X2) X0) = (σ (k X2 (k (τ (M.op (M.op X0 X0) X0)) (M.op (M.op (τ X0) (M.op X1 X1)) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq151243 (M.op (M.op X0 X0) X0) (M.op (M.op (τ X0) (M.op X1 X1)) X1) X2
       have i₂ := eq497204 X0 X1
       grind)
    | exact superpose eq497204 eq151243
    | exact resolve eq151243 eq497204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497204
  have eq866704 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X2) (σ X0)) ∨ (M.op (σ X2) (σ X0)) = (σ (k X2 (k (τ (τ (τ (τ (M.op (M.op (σ (σ (σ (σ X0)))) (M.op X1 X1)) X1))))) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq151243 (τ (τ (τ (M.op (M.op (σ (σ (σ (σ X1)))) (M.op X1 X1)) X1)))) X1 X2
       have i₂ := eq4245 (σ X1) X1
       grind)
    | exact superpose eq4245 eq151243
    | exact resolve eq151243 eq4245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4245 eq151243
  have eq866950 : ∀ X0 X2 : G, (σ X0) = (M.op (σ X2) (σ X0)) ∨ (M.op (σ X2) (σ X0)) = (σ (k X2 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq866704 X0 x X2
       have i₂ := eq153197 X0 x
       grind)
    | exact superpose eq153197 eq866704
    | (have j0 := eq866704 X0 x X2
       grind)
    | exact resolve eq866704 eq153197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153197 eq866704
  have eq867035 : ∀ X0 X2 : G, (M.op (σ X2) X0) = (σ (k X2 (τ X0))) ∨ (M.op (σ X2) X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq866618 X0 x X2
       have i₂ := eq329456 X0 x
       grind)
    | exact superpose eq329456 eq866618
    | (have j0 := eq866618 X0 x X2
       grind)
    | exact resolve eq866618 eq329456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329456 eq866618
  have eq867251 : ∀ X0 X2 : G, (M.op (σ X2) X0) = (k (σ X2) X0) ∨ (M.op (σ X2) X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq867035 X0 X2
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq867035
    | (have j0 := eq867035 X0 X2
       grind)
    | exact resolve eq867035 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq867035
  have eq867553 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq867251 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq867251
    | exact resolve eq867251 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867251
  have eq869090 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq867553 (τ X0) X1
       grind)
    | exact superpose eq867553 eq17
    | (have j1 := eq867553 (τ X0) X1
       grind)
    | exact resolve eq17 eq867553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq867553
  have eq875647 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq869090 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq869090
    | exact resolve eq869090 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869090
  have eq876658 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq875647 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq875647
    | (have j0 := eq875647 X0 X1
       grind)
    | exact resolve eq875647 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875647
  have eq887127 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (τ (M.op (M.op (M.op (σ X0) (M.op X2 X2)) X2) (σ X0))) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq194881 X1 (σ X0) X2
       have i₂ := eq866950 X0 X1
       grind)
    | exact superpose eq866950 eq194881
    | (have j1 := eq866950 X0 X1
       grind)
    | exact resolve eq194881 eq866950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194881 eq866950
  have eq889034 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq887127 X0 X1 x
       have i₂ := eq351 (σ X0) x
       grind)
    | exact superpose eq351 eq887127
    | (have j0 := eq887127 X0 X1 x
       grind)
    | exact resolve eq887127 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351 eq887127
  have eq889732 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq889034 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq889034
    | (have j0 := eq889034 X0 X1
       grind)
    | exact resolve eq889034 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889034
  have eq890764 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq889732 y x
       grind)
    | exact superpose eq889732 eq16
    | (have j1 := eq889732 y x
       grind)
    | exact resolve eq16 eq889732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889732
  have eq895297 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq890764
       have i₂ := eq876658 x y
       grind)
    | exact superpose eq876658 eq890764
    | (have j1 := eq876658 x y
       grind)
    | (have r₁ := eq890764
       have r₂ := eq876658 x y
       grind)
    | exact resolve eq890764 eq876658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876658 eq890764
  have eq895300 : y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq895297
  have eq895350 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op y (τ (M.op X0 X0))) (τ X0)) y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq76397 X0 x y
       have i₂ := eq895300
       grind)
    | exact superpose eq895300 eq76397
    | exact resolve eq76397 eq895300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76397 eq895300
  have eq895383 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq895350 x
       have i₂ := eq5367 x y
       grind)
    | exact superpose eq5367 eq895350
    | exact resolve eq895350 eq5367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5367 eq895350
  have eq895384 : y = (M.op x x) := by grind
  clear eq895383
  have eq896557 : y = (M.op x y) := by
    first
    | (have i₁ := eq420 x
       have i₂ := eq895384
       grind)
    | exact superpose eq895384 eq420
    | exact resolve eq420 eq895384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq896774 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5611 x
       have i₂ := eq895384
       grind)
    | exact superpose eq895384 eq5611
    | exact resolve eq5611 eq895384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5611 eq895384
  have eq911574 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq896774
       grind)
    | exact superpose eq896774 eq16
    | exact resolve eq16 eq896774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896774
  have eq911777 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq911574
       have i₂ := eq896557
       grind)
    | exact superpose eq896557 eq911574
    | exact resolve eq911574 eq896557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896557 eq911574
  have eq911778 : False := by grind
  exact eq911778
