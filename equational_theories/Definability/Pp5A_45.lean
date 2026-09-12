import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation690`: `x = y ◇ (x ◇ ((z ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_pxy_x_pxy_Equation690 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law690 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law690.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X2 X1) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X0)) (M.op X3 (M.op X0 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X0 (M.op (M.op X1 X2) X0)) X2
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X4 : G, (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X4 (M.op (M.op X0 (M.op X1 X0)) X4))) = X4 := by
    intro X0 X1 X4
    first
    | (have i₁ := eq62 (M.op X0 (M.op X1 X0)) X1 (M.op (M.op x x) X1) X4
       have i₂ := eq62 X1 x x X0
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X2 (M.op X0 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op X1 X0)) (M.op X1 (M.op (M.op x x) X1))
       have i₂ := eq62 X1 x x X0
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq92 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) (M.op X2 (M.op X0 X1))) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80 (M.op X0 X1) X2 (M.op X1 (M.op X0 X1))
       have i₂ := eq80 X1 X0 (M.op X0 X1)
       grind)
    | exact superpose eq80 eq80
    | exact resolve eq80 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (M.op (M.op X1 X2) (M.op (M.op X0 (M.op X2 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X2 X0)) (M.op X1 X2) X2
       have i₂ := eq80 X2 X1 X0
       grind)
    | exact superpose eq80 eq9
    | exact resolve eq9 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq14 X0 (M.op X1 (M.op X0 X0))
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq349 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq354 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq330 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq355 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq354 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq356 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq350 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq350 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq350 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq369 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq356 (σ X0)
       grind)
    | exact superpose eq356 eq15
    | exact resolve eq15 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq388 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq369 X0
       have i₂ := eq356 X0
       grind)
    | exact superpose eq356 eq369
    | exact resolve eq369 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356 eq369
  have eq482 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq355 X0 (τ X1)
       grind)
    | exact superpose eq355 eq19
    | (have j1 := eq355 X0 (τ X1)
       grind)
    | exact resolve eq19 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq485 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq355 (σ X0) (σ X1)
       grind)
    | exact superpose eq355 eq15
    | (have j1 := eq355 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq508 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq485 X0 X1
       have i₂ := eq388 X0
       grind)
    | exact superpose eq388 eq485
    | (have j0 := eq485 X0 X1
       grind)
    | exact resolve eq485 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq707 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq482 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq482
    | exact resolve eq482 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq749 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq707 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq707
    | (have j0 := eq707 X0 X1
       grind)
    | exact resolve eq707 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq1371 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq508 x y
       grind)
    | exact superpose eq508 eq16
    | (have j1 := eq508 x y
       grind)
    | exact resolve eq16 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq1438 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1371
       have i₂ := eq749 y x
       grind)
    | exact superpose eq749 eq1371
    | (have j1 := eq749 y x
       grind)
    | (have r₁ := eq1371
       have r₂ := eq749 y x
       grind)
    | exact resolve eq1371 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749 eq1371
  have eq1439 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq1438
  have eq1460 : ∀ X0 : G, x = (M.op (M.op x (M.op X0 x)) (M.op x y)) ∨ (σ y) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq80 x X0 x
       have i₂ := eq1439
       grind)
    | exact superpose eq1439 eq80
    | exact resolve eq80 eq1439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439
  have eq1523 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq94 (M.op X0 (M.op X1 X0)) X1 (M.op X1 X0)
       have i₂ := eq80 X0 X1 (M.op X1 X0)
       grind)
    | exact superpose eq80 eq94
    | exact resolve eq94 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4484 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op (M.op X0 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80 X0 X1 (M.op (M.op X0 (M.op X2 X0)) X0)
       have i₂ := eq72 X0 X2 X0
       grind)
    | exact superpose eq72 eq80
    | exact resolve eq80 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4673 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X3 (M.op (M.op X0 (M.op X2 X0)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq72 X0 X2 X3
       have i₂ := eq4484 X0 X2 X1
       grind)
    | (have i₁ := eq72 X0 X2 X3
       have i₂ := eq4484 X0 X1 X2
       grind)
    | exact superpose eq4484 eq72
    | exact resolve eq72 eq4484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4674 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X2 X0)) = (M.op (M.op X3 X2) (M.op (M.op X0 (M.op X1 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq94 X0 X3 X2
       have i₂ := eq4484 X0 X2 X1
       grind)
    | (have i₁ := eq94 X0 X3 X2
       have i₂ := eq4484 X0 X1 X2
       grind)
    | exact superpose eq4484 eq94
    | exact resolve eq94 eq4484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq4484
  have eq5013 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op (M.op (M.op X0 (M.op X3 X0)) X0) X2)) = (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X2 (M.op X5 X2)) X2)) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq4674 X2 X5 (M.op (M.op X0 (M.op X3 X0)) X0) (M.op x X1)
       have i₂ := eq4674 X0 X3 X1 x
       grind)
    | exact superpose eq4674 eq4674
    | exact resolve eq4674 eq4674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5241 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op (M.op X0 (M.op X3 X0)) X0) X2)) = (M.op X2 (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5013 X0 X1 X2 X3 x
       have i₂ := eq4674 X2 x (M.op X1 X0) X0
       grind)
    | exact superpose eq4674 eq5013
    | exact resolve eq5013 eq4674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5013
  have eq6475 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X2 (M.op X1 X0))) = (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4674 (M.op X1 X0) x X2 X3
       have i₂ := eq92 X1 X0 x
       grind)
    | exact superpose eq92 eq4674
    | exact resolve eq4674 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq10455 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X3 (M.op X1 (M.op X4 X1))) X0)) = (M.op (M.op (M.op X1 (M.op X2 X1)) X1) (M.op (M.op X0 (M.op (M.op X3 (M.op X1 (M.op X4 X1))) X0)) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq4673 X1 X2 X4 (M.op X0 (M.op (M.op X3 (M.op X1 (M.op X4 X1))) X0))
       have i₂ := eq9 X0 (M.op X1 (M.op X4 X1)) X3
       grind)
    | exact superpose eq9 eq4673
    | exact resolve eq4673 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10595 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op (M.op X3 (M.op X1 (M.op X4 X1))) X0)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq10455 X0 X1 x X3 X4
       have i₂ := eq4674 X0 (M.op X3 (M.op X1 (M.op X4 X1))) X1 (M.op X1 (M.op x X1))
       grind)
    | exact superpose eq4674 eq10455
    | exact resolve eq10455 eq4674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4674 eq10455
  have eq15409 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op (M.op X1 X2) X0)) = (M.op X0 (M.op (M.op X4 X2) X0)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq5241 X2 X4 X0 x
       have i₂ := eq5241 X2 X1 X0 x
       grind)
    | (have i₁ := eq5241 X0 X1 X2 x
       have i₂ := eq5241 X0 (M.op X0 (M.op x X0)) X2 x
       grind)
    | exact superpose eq5241 eq5241
    | exact resolve eq5241 eq5241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5241
  have eq16155 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ (M.op X0 X0)) X1)) = (M.op X1 (M.op (M.op X2 (σ X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15409 X1 X2 (σ X0) (σ X0)
       have i₂ := eq388 X0
       grind)
    | exact superpose eq388 eq15409
    | exact resolve eq15409 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16504 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X2 X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1523 X1 X0 X0
       have i₂ := eq15409 (M.op X0 (M.op X1 X0)) X1 X0 X2
       grind)
    | (have i₁ := eq1523 X1 X0 X0
       have i₂ := eq15409 (M.op X0 (M.op X1 X0)) X2 X0 X1
       grind)
    | exact superpose eq15409 eq1523
    | exact resolve eq1523 eq15409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1523 eq15409
  have eq18270 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X3 X2)) (M.op X4 (M.op (M.op (M.op X0 X1) (M.op X2 (M.op X3 X2))) X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X4 (M.op X1 (M.op X3 X2)) (M.op X3 X2)
       have i₂ := eq6475 X2 X3 X1 X0
       grind)
    | (have i₁ := eq9 X0 (M.op X0 (M.op X1 X0)) (M.op X3 X2)
       have i₂ := eq6475 X0 X1 X2 X3
       grind)
    | exact superpose eq6475 eq9
    | exact resolve eq9 eq6475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18319 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80 X0 X2 X1
       have i₂ := eq6475 X1 X0 (M.op X2 X0) X0
       grind)
    | (have i₁ := eq80 X1 X1 (M.op X1 X1)
       have i₂ := eq6475 (M.op X1 X1) X1 (M.op X1 X1) x
       grind)
    | exact superpose eq6475 eq80
    | exact resolve eq80 eq6475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq18583 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X3 X2)) (M.op X4 (M.op X2 X4))) = X4 := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq18270 x X1 X2 X3 X4
       have i₂ := eq10595 X4 X2 (M.op x X1) X3
       grind)
    | exact superpose eq10595 eq18270
    | exact resolve eq18270 eq10595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18270
  have eq18756 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X1 (M.op X3 X1))) X0) = (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X4 X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq18319 X0 (M.op (M.op X3 (M.op X1 (M.op X4 X1))) X0) X2
       have i₂ := eq10595 X0 X1 X3 X4
       grind)
    | exact superpose eq10595 eq18319
    | exact resolve eq18319 eq10595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18761 : ∀ X0 X1 X2 X3 : G, (M.op (σ (M.op X2 X2)) X0) = (M.op (M.op X0 (M.op (M.op X1 (σ X2)) X0)) (M.op (M.op X3 X0) (M.op X0 (M.op (M.op X1 (σ X2)) X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18319 X1 (M.op (σ (M.op X0 X0)) X1) X2
       have i₂ := eq16155 X0 X1 X2
       grind)
    | exact superpose eq16155 eq18319
    | exact resolve eq18319 eq16155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16155
  have eq18814 : ∀ X0 X1 : G, (M.op x y) = (M.op x (M.op (M.op X1 (M.op x (M.op X0 x))) x)) ∨ (σ y) = (σ (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq18319 (M.op x (M.op X0 x)) (M.op x y) x
       have i₂ := eq1460 X0
       grind)
    | exact superpose eq1460 eq18319
    | exact resolve eq18319 eq1460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1460
  have eq18882 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) X0) = (M.op (M.op (M.op X1 (M.op X2 X1)) X1) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4673 X1 X2 X3 (M.op (M.op X3 X1) X0)
       have i₂ := eq18319 (M.op X3 X1) X0 X1
       grind)
    | exact superpose eq18319 eq4673
    | exact resolve eq4673 eq18319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4673
  have eq18883 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op (M.op X1 (M.op X2 X1)) X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 X1 X2 (M.op (M.op X2 X1) X0)
       have i₂ := eq18319 (M.op X2 X1) X0 X1
       grind)
    | exact superpose eq18319 eq72
    | exact resolve eq72 eq18319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq19007 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X3 X1) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18882 X0 X1 X3 X2
       have i₂ := eq18883 X0 X1 X3
       grind)
    | exact superpose eq18883 eq18882
    | exact resolve eq18882 eq18883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18882 eq18883
  have eq19013 : (σ y) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq18814 x x
       have i₂ := eq10595 x x x x
       grind)
    | exact superpose eq10595 eq18814
    | exact resolve eq18814 eq10595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10595 eq18814
  have eq19026 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X2 X2)) X0) = (M.op (M.op X1 (σ X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18761 X0 X1 X2 x
       have i₂ := eq16504 X0 (M.op X1 (σ X2)) x
       grind)
    | exact superpose eq16504 eq18761
    | exact resolve eq18761 eq16504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18761
  have eq19031 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X1 (M.op X3 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18756 X0 X1 X2 X3 x
       have i₂ := eq16504 X0 X1 x
       grind)
    | exact superpose eq16504 eq18756
    | exact resolve eq18756 eq16504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16504 eq18756
  have eq19275 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) (M.op X2 (M.op X3 X2))) X5) = (M.op (M.op X4 (M.op X1 (M.op X3 X2))) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq19007 X5 (M.op X1 (M.op X3 X2)) X4 (M.op X3 X2)
       have i₂ := eq6475 X2 X3 X1 X0
       grind)
    | (have i₁ := eq19007 X0 (M.op X0 (M.op X1 X0)) X2 (M.op X3 X2)
       have i₂ := eq6475 X0 X1 X2 X3
       grind)
    | exact superpose eq6475 eq19007
    | exact resolve eq19007 eq6475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19852 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 (M.op (M.op X3 (M.op X4 X1)) X2))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X2 (M.op X4 X1) X3
       have i₂ := eq19007 (M.op X2 (M.op (M.op X3 (M.op X4 X1)) X2)) X1 X4 X0
       grind)
    | (have i₁ := eq9 X2 (M.op X4 X1) X3
       have i₂ := eq19007 (M.op X2 (M.op (M.op X3 (M.op X4 X1)) X2)) X1 X0 X4
       grind)
    | exact superpose eq19007 eq9
    | exact resolve eq9 eq19007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19993 : ∀ X1 X2 X3 X4 X5 : G, (M.op X2 X5) = (M.op (M.op X4 (M.op X1 (M.op X3 X2))) X5) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq19275 x X1 X2 X3 X4 X5
       have i₂ := eq19031 X5 X2 (M.op x X1) X3
       grind)
    | exact superpose eq19031 eq19275
    | exact resolve eq19275 eq19031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19031 eq19275
  have eq22617 : ∀ X0 X1 X2 : G, (M.op (σ X0) X1) = (M.op (M.op X2 (σ (M.op X0 (M.op X0 X0)))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19026 X1 X2 (M.op X0 (M.op X0 X0))
       have i₂ := eq18583 X0 X0 X0 X0
       grind)
    | exact superpose eq18583 eq19026
    | exact resolve eq19026 eq18583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18583
  have eq23463 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) X1) = (M.op (M.op X2 (M.op X3 (σ (M.op X0 X0)))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19993 X3 (σ X0) (σ X0) X2 X1
       have i₂ := eq388 X0
       grind)
    | exact superpose eq388 eq19993
    | exact resolve eq19993 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27093 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X5 X4) = (M.op (M.op X6 X3) (M.op (M.op X0 (M.op X1 (M.op X2 X3))) (M.op X4 (M.op X5 X4)))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq19852 X6 X3 (M.op X5 X4) X1 X2
       have i₂ := eq6475 X4 X5 (M.op X1 (M.op X2 X3)) X0
       grind)
    | (have i₁ := eq19852 X0 X1 (M.op X1 (M.op X3 (M.op X4 X1))) X3 X4
       have i₂ := eq6475 (M.op X3 (M.op X4 X1)) X1 (M.op X3 (M.op X4 X1)) X1
       grind)
    | exact superpose eq6475 eq19852
    | exact resolve eq19852 eq6475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19852
  have eq27380 : ∀ X3 X4 X5 X6 : G, (M.op X5 X4) = (M.op (M.op X6 X3) (M.op X3 (M.op X4 (M.op X5 X4)))) := by
    intro X3 X4 X5 X6
    first
    | (have i₁ := eq27093 x x x X3 X4 X5 X6
       have i₂ := eq19993 x X3 x x (M.op X4 (M.op X5 X4))
       grind)
    | exact superpose eq19993 eq27093
    | exact resolve eq27093 eq19993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19993 eq27093
  have eq43417 : (M.op x x) = (τ (σ y)) ∨ (M.op x y) = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq19013
       grind)
    | exact superpose eq19013 eq10
    | exact resolve eq10 eq19013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19013
  have eq43497 : (M.op x y) = (M.op x (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq43417
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq43417
    | exact resolve eq43417 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43417
  have eq43613 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) (M.op (M.op X0 x) (M.op x y))) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq18319 x (M.op x x) x
       have i₂ := eq43497
       grind)
    | exact superpose eq43497 eq18319
    | exact resolve eq18319 eq43497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43497
  have eq43661 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq43613 x
       have i₂ := eq18319 x y x
       grind)
    | exact superpose eq18319 eq43613
    | exact resolve eq43613 eq18319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43613
  have eq43662 : y = (M.op x x) := by grind
  clear eq43661
  have eq43743 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op X1 (σ x)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19026 X0 X1 x
       have i₂ := eq43662
       grind)
    | exact superpose eq43662 eq19026
    | exact resolve eq19026 eq43662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19026
  have eq43750 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op X1 (σ (M.op x y))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22617 x X0 X1
       have i₂ := eq43662
       grind)
    | exact superpose eq43662 eq22617
    | exact resolve eq22617 eq43662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22617
  have eq43752 : ∀ X0 X1 X2 : G, (M.op (σ x) X0) = (M.op (M.op X1 (M.op X2 (σ y))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23463 x X0 X1 X2
       have i₂ := eq43662
       grind)
    | exact superpose eq43662 eq23463
    | exact resolve eq23463 eq43662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23463
  have eq43791 : ∀ X0 X1 : G, (M.op y (M.op X0 y)) = (M.op (M.op X1 X0) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq6475 x x x x
       have i₂ := eq43662
       grind)
    | exact superpose eq43662 eq6475
    | exact resolve eq6475 eq43662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43807 : ∀ X0 : G, x = (M.op y (M.op (M.op X0 x) y)) := by
    intro X0
    first
    | (have i₁ := eq18319 x x x
       have i₂ := eq43662
       grind)
    | exact superpose eq43662 eq18319
    | exact resolve eq18319 eq43662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43817 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19007 X1 x X0 x
       have i₂ := eq43662
       grind)
    | exact superpose eq43662 eq19007
    | exact resolve eq19007 eq43662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19007
  have eq43847 : x = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq43807 x
       have i₂ := eq43817 x y
       grind)
    | exact superpose eq43817 eq43807
    | exact resolve eq43807 eq43817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43807 eq43817
  have eq45940 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 (M.op X1 X0))) = (M.op (M.op X1 X0) (M.op (σ x) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6475 X0 X1 (σ x) x
       have i₂ := eq43743 (M.op X0 (M.op X1 X0)) x
       grind)
    | exact superpose eq43743 eq6475
    | exact resolve eq6475 eq43743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6475 eq43743
  have eq60496 : ∀ X0 : G, (M.op (M.op (σ (M.op x y)) X0) (M.op (σ x) (M.op (σ (M.op x y)) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq18319 (σ (M.op x y)) X0 x
       have i₂ := eq43750 (M.op (σ (M.op x y)) X0) x
       grind)
    | exact superpose eq43750 eq18319
    | exact resolve eq18319 eq43750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43750
  have eq60929 : ∀ X0 : G, (M.op (σ y) (M.op X0 (M.op (σ (M.op x y)) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq60496 X0
       have i₂ := eq45940 X0 (σ (M.op x y))
       grind)
    | exact superpose eq45940 eq60496
    | exact resolve eq60496 eq45940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45940 eq60496
  have eq76494 : ∀ X0 X1 : G, (M.op (M.op X1 (σ y)) X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq27380 (σ y) X0 (σ (M.op x y)) X1
       have i₂ := eq60929 X0
       grind)
    | exact superpose eq60929 eq27380
    | exact resolve eq27380 eq60929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27380 eq60929
  have eq91211 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op X0 (σ y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq388 (M.op x y)
       have i₂ := eq76494 (σ (M.op x y)) X0
       grind)
    | exact superpose eq76494 eq388
    | exact resolve eq388 eq76494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76494
  have eq91739 : ∀ X0 : G, (σ (M.op y (M.op y y))) = (M.op (M.op X0 (σ y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq91211 X0
       have i₂ := eq43791 y x
       grind)
    | exact superpose eq43791 eq91211
    | exact resolve eq91211 eq43791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43791 eq91211
  have eq91911 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq91739 X0
       have i₂ := eq43847
       grind)
    | exact superpose eq43847 eq91739
    | exact resolve eq91739 eq43847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43847 eq91739
  have eq92114 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (M.op X1 (M.op X0 (σ y))) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq18319 (M.op X0 (σ y)) (σ (M.op x y)) x
       have i₂ := eq91911 X0
       grind)
    | exact superpose eq91911 eq18319
    | exact resolve eq18319 eq91911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18319 eq91911
  have eq92189 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq92114 x x
       have i₂ := eq43752 (σ x) x x
       grind)
    | exact superpose eq43752 eq92114
    | exact resolve eq92114 eq43752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43752 eq92114
  have eq92239 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq92189
       have i₂ := eq388 x
       grind)
    | exact superpose eq388 eq92189
    | exact resolve eq92189 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388 eq92189
  have eq92260 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq92239
       have i₂ := eq43662
       grind)
    | exact superpose eq43662 eq92239
    | exact resolve eq92239 eq43662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43662 eq92239
  have eq92270 : False := by grind
  exact eq92270

/-- `Equation72`: `x = y ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_y_pxy_Equation72 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law72 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law72.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
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
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq35 (M.op X0 X0)
       grind)
    | exact superpose eq35 eq14
    | exact resolve eq14 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq38 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq39 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq40 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq47 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq46
  have eq50 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq53 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq50
  have eq54 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq53
  have eq58 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq51
       grind)
    | exact superpose eq51 eq16
    | exact resolve eq16 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq54
       grind)
    | exact superpose eq54 eq16
    | exact resolve eq16 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq51
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq51
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq51 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq75
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq75
    | exact resolve eq75 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq81
    | exact resolve eq81 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq83
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq83
    | exact resolve eq83 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq91 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq39
    | (have j0 := eq39 y
       grind)
    | exact resolve eq39 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq95 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq91
  have eq96 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq95
  have eq110 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq40
    | (have j0 := eq40 (M.op x y)
       grind)
    | exact resolve eq40 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq113 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by grind
  clear eq110
  have eq114 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq113
  have eq127 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq16
    | exact resolve eq16 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq114 eq16
    | exact resolve eq16 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq16
    | exact resolve eq16 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq390 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1
       have i₂ := eq47 X0
       grind)
    | exact superpose eq47 eq14
    | exact resolve eq14 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq434 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 X1
       have i₂ := eq47 X1
       grind)
    | exact superpose eq47 eq72
    | (have j0 := eq72 X0 X1
       grind)
    | exact resolve eq72 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq72
  have eq452 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq21 eq251
    | (have j0 := eq251 X0 (M.op x y)
       grind)
    | exact resolve eq251 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq536 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq434 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq434
    | (have j0 := eq434 x X0
       grind)
    | exact resolve eq434 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq558 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq434 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq3147 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) X1
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq14
    | exact resolve eq14 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3148 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq35 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq35
    | exact resolve eq35 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq4288 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq536 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq536
    | (have j0 := eq536 y
       grind)
    | exact resolve eq536 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq4296 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4288
       have i₂ := eq51
       grind)
    | exact superpose eq51 eq4288
    | exact resolve eq4288 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4288
  have eq4315 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq4296
    | exact resolve eq4296 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4296
  have eq4323 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4315
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq4315
    | exact resolve eq4315 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4315
  have eq4328 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq4323
    | exact resolve eq4323 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4323
  have eq6049 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op x y))) ≠ (σ (τ (k X0 (σ (M.op x y))))) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (τ X0)) (σ (M.op x y))) ∨ (σ (τ X0)) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq452 eq558
    | (have j0 := eq558 (τ X0) (M.op x y)
       grind)
    | exact resolve eq558 eq452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452 eq558
  have eq6143 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op x y))) ≠ (k X0 (σ (M.op x y))) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (τ X0)) (σ (M.op x y))) ∨ (σ (τ X0)) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq6049 X0
       have i₂ := eq15 (k X0 sF1)
       grind)
    | exact superpose eq15 eq6049
    | (have j0 := eq6049 X0
       grind)
    | exact resolve eq6049 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6049
  have eq6193 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (k X0 (σ (M.op x y))) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (τ X0)) (σ (M.op x y))) ∨ (σ (τ X0)) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq114 eq6143
    | (have j0 := eq6143 X0
       grind)
    | exact resolve eq6143 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6143
  have eq6238 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (τ X0)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (k X0 (σ (M.op x y))) ∨ (σ (τ X0)) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21 eq6193
    | (have j0 := eq6193 X0
       grind)
    | exact resolve eq6193 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6193
  have eq6280 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (k X0 (σ (M.op x y))) ∨ (σ (τ X0)) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq6238 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6238
    | (have j0 := eq6238 X0
       grind)
    | exact resolve eq6238 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6238
  have eq6321 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (k X0 (σ (M.op x y))) ∨ (σ (τ X0)) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq114 eq6280
    | (have j0 := eq6280 X0
       grind)
    | exact resolve eq6280 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq6280
  have eq6361 : ∀ X0 : G, (σ (τ X0)) = (σ (M.op x y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq6321
    | (have j0 := eq6321 X0
       grind)
    | exact resolve eq6321 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6321
  have eq6366 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (k X0 (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq6361 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6361
    | (have j0 := eq6361 X0
       grind)
    | exact resolve eq6361 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6361
  have eq8616 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq84 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8617 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq8616
    | exact resolve eq8616 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8616
  have eq8628 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq8617
       have r₂ := eq28
       grind)
    | exact resolve eq8617 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8617
  have eq8632 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq8628
    | exact resolve eq8628 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8628
  have eq8641 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (σ y) = (k X0 (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq8632 eq12
    | (have j0 := eq12 (σ y) X0
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq8632
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq8632
       grind)
    | exact resolve eq12 eq8632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8632
  have eq14457 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3147 X1 X2
       have i₂ := eq3147 X1 X0
       grind)
    | exact superpose eq3147 eq3147
    | exact resolve eq3147 eq3147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14521 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3148 X1
       have i₂ := eq3147 X1 X0
       grind)
    | exact superpose eq3147 eq3148
    | exact resolve eq3148 eq3147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85348 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq8641
    | (have j0 := eq8641 (σ x)
       grind)
    | (have r₁ := eq8641 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq8641 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8641
  have eq85354 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq85348
  have eq85355 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq85354
  have eq86210 : (τ (σ y)) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq85355 eq58
    | exact resolve eq58 eq85355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq86211 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq85355 eq84
    | exact resolve eq84 eq85355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq85355
  have eq86225 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq86211
  have eq86236 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | exact superpose eq30 eq86210
    | exact resolve eq86210 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86210
  have eq86245 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq86225
       grind)
    | exact superpose eq86225 eq96
    | exact resolve eq96 eq86225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86262 : y = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq86225
       grind)
    | exact superpose eq86225 eq36
    | exact resolve eq36 eq86225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq86265 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq390 y X0
       have i₂ := eq86225
       grind)
    | exact superpose eq86225 eq390
    | exact resolve eq390 eq86225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86281 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 (M.op X0 y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq3147 y x
       have i₂ := eq86225
       grind)
    | exact superpose eq86225 eq3147
    | exact resolve eq3147 eq86225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86285 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3147 y y
       have i₂ := eq86225
       grind)
    | exact superpose eq86225 eq3147
    | exact resolve eq3147 eq86225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86225
  have eq86294 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq21 eq86265
    | (have j0 := eq86265 X0
       grind)
    | exact resolve eq86265 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86265
  have eq86309 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq86245
    | exact resolve eq86245 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86245
  have eq86318 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq86294 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq86294
    | (have j0 := eq86294 X0
       grind)
    | exact resolve eq86294 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86294
  have eq88910 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14 y X0
       have i₂ := eq86236
       grind)
    | exact superpose eq86236 eq14
    | exact resolve eq14 eq86236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88931 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 (M.op X0 y)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq3147 y x
       have i₂ := eq86236
       grind)
    | exact superpose eq86236 eq3147
    | exact resolve eq3147 eq86236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88935 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq3147 y y
       have i₂ := eq86236
       grind)
    | exact superpose eq86236 eq3147
    | exact resolve eq3147 eq86236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86236
  have eq89024 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 (σ (M.op y (M.op x y))))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq86285 eq390
    | exact resolve eq390 eq86285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89055 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 (σ (M.op y (M.op x y))))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq21 eq89024
    | (have j0 := eq89024 X0
       grind)
    | exact resolve eq89024 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89024
  have eq94326 : y = (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq86285 eq86262
    | exact resolve eq86262 eq86285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86285
  have eq94366 : y = (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq94326
  have eq94439 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq86281 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq86281
    | (have j0 := eq86281 x
       grind)
    | exact resolve eq86281 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86281
  have eq95243 : y = (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq94439 eq86262
    | exact resolve eq86262 eq94439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86262 eq94439
  have eq95279 : y = (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq95243
  have eq108127 : ∀ X0 : G, (σ (M.op y (M.op x y))) = (M.op X0 (M.op X0 (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq94366 eq390
    | exact resolve eq390 eq94366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94366
  have eq108159 : ∀ X0 : G, (σ (M.op y (M.op x y))) = (M.op X0 (M.op X0 (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq108127 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq108127
    | (have j0 := eq108127 X0
       grind)
    | exact resolve eq108127 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108127
  have eq110765 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 (M.op x (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq95279 eq3147
    | exact resolve eq3147 eq95279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95279
  have eq128506 : (σ (M.op y (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq108159
    | (have j0 := eq108159 (σ x)
       grind)
    | exact resolve eq108159 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108159
  have eq129425 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq128506 eq89055
    | exact resolve eq89055 eq128506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89055 eq128506
  have eq129549 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq129425 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129425
  have eq132106 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq129549 eq14
    | exact resolve eq14 eq129549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129549
  have eq133261 : (σ y) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq132106 eq86318
    | exact resolve eq86318 eq132106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86318 eq132106
  have eq133264 : (σ y) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq133261
  have eq261376 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq88931 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq88931
    | (have j0 := eq88931 x
       grind)
    | exact resolve eq88931 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88931
  have eq261523 : (M.op x (M.op x y)) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | exact superpose eq261376 eq88935
    | exact resolve eq88935 eq261376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88935 eq261376
  have eq261625 : (M.op x (M.op x y)) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by grind
  clear eq261523
  have eq335174 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | exact superpose eq88910 eq110765
    | exact resolve eq110765 eq88910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88910 eq110765
  have eq335260 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k x y) := by grind
  clear eq335174
  have eq335276 : y = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq335260
       have r₂ := eq12 x y
       grind)
    | exact resolve eq335260 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335260
  have eq335281 : (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq51
       have i₂ := eq335276
       grind)
    | exact superpose eq335276 eq51
    | exact resolve eq51 eq335276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335276
  have eq335336 : (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq335281
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq335281
    | exact resolve eq335281 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335281
  have eq335385 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq335336 eq4328
    | exact resolve eq4328 eq335336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4328 eq335336
  have eq335401 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq335385
  have eq335484 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq335401 eq86309
    | exact resolve eq86309 eq335401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335401
  have eq335655 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq335484
  have eq335720 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq335655
       have r₂ := eq28
       grind)
    | exact resolve eq335655 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335655
  have eq336082 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq335720 eq133264
    | exact resolve eq133264 eq335720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133264
  have eq336269 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq336082
  have eq336671 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq336269
    | exact resolve eq336269 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336269
  have eq336722 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq335720 eq336671
    | exact resolve eq336671 eq335720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335720 eq336671
  have eq336966 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq336722
  have eq337602 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq336966 eq86309
    | exact resolve eq86309 eq336966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86309 eq336966
  have eq337762 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq337602
  have eq337865 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq337762 eq30
    | exact resolve eq30 eq337762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337762
  have eq338019 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq337865
    | exact resolve eq337865 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq337865
  have eq338020 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq338019
  have eq338044 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq338020 eq27
    | exact resolve eq27 eq338020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338045 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq338020 eq30
    | exact resolve eq30 eq338020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq338060 : (M.op y y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = y := by
    first
    | exact superpose eq338020 eq127
    | exact resolve eq127 eq338020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq339055 : (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq160 eq338060
    | exact resolve eq338060 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq338060
  have eq339069 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq338045
    | exact resolve eq338045 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq338045
  have eq341110 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq339069 eq261625
    | exact resolve eq261625 eq339069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261625
  have eq341199 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by grind
  clear eq341110
  have eq341465 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq341199
       have r₂ := eq12 x y
       grind)
    | exact resolve eq341199 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341199
  have eq343521 : (M.op x y) = (M.op (M.op x y) (M.op (M.op y y) (M.op y y))) ∨ x = y := by
    first
    | exact superpose eq339055 eq3148
    | exact resolve eq3148 eq339055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3148 eq339055
  have eq357991 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq51
       have i₂ := eq341465
       grind)
    | exact superpose eq341465 eq51
    | exact resolve eq51 eq341465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq341465
  have eq358048 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq357991
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq357991
    | exact resolve eq357991 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357991
  have eq359055 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq338020 eq358048
    | exact resolve eq358048 eq338020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358048
  have eq359098 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq359055
  have eq435381 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op X0 (M.op X0 y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq343521
       have i₂ := eq3147 y X0
       grind)
    | exact superpose eq3147 eq343521
    | exact resolve eq343521 eq3147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343521
  have eq435440 : (M.op x y) = (M.op (M.op x y) (M.op x (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq435381 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq435381
    | (have j0 := eq435381 x
       grind)
    | exact resolve eq435381 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435381
  have eq435541 : y = (M.op y (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq339069 eq435440
    | exact resolve eq435440 eq339069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435440
  have eq435572 : y = (M.op y (M.op x y)) ∨ x = y := by grind
  clear eq435541
  have eq435573 : y = (M.op y (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq435572
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq435572
    | exact resolve eq435572 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435572
  have eq435574 : y = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq339069 eq435573
    | exact resolve eq435573 eq339069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339069 eq435573
  have eq435780 : y = (M.op y y) ∨ x = y := by grind
  clear eq435574
  have eq435789 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq96
       have i₂ := eq435780
       grind)
    | exact superpose eq435780 eq96
    | exact resolve eq96 eq435780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq435935 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq390 y X0
       have i₂ := eq435780
       grind)
    | exact superpose eq435780 eq390
    | exact resolve eq390 eq435780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390 eq435780
  have eq436100 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq435935 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq435935
    | (have j0 := eq435935 X0
       grind)
    | exact resolve eq435935 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435935
  have eq436115 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq435789
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq435789
    | exact resolve eq435789 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435789
  have eq436140 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq338020 eq436115
    | exact resolve eq436115 eq338020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436115
  have eq436500 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq436140
  have eq439677 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq338020 eq436100
    | exact resolve eq436100 eq338020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338020
  have eq439717 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq27 eq436100
    | (have j0 := eq436100 (σ x)
       grind)
    | exact resolve eq436100 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436100
  have eq439874 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq439677 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439677
  have eq441054 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq338044 eq439874
    | exact resolve eq439874 eq338044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338044 eq439874
  have eq441147 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y := by grind
  clear eq441054
  have eq678326 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq439717 eq14521
    | exact resolve eq14521 eq439717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439717
  have eq678664 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq27 eq678326
    | exact resolve eq678326 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678326
  have eq678858 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq678664 eq3147
    | exact resolve eq3147 eq678664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3147 eq678664
  have eq688062 : (M.op (σ x) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq441147 eq678858
    | exact resolve eq678858 eq441147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441147 eq678858
  have eq688199 : (M.op (σ x) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y := by grind
  clear eq688062
  have eq688364 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (σ (M.op x y))))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq688199 eq14
    | exact resolve eq14 eq688199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688199
  have eq697896 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (M.op X0 (σ (M.op x y))))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq688364 sF2
       have i₂ := eq14457 sF2 sF1 x
       grind)
    | (have i₁ := eq688364 sF2
       have i₂ := eq14457 X0 sF1 sF2
       grind)
    | exact superpose eq14457 eq688364
    | exact resolve eq688364 eq14457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14457
  have eq1680542 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq359098 eq6366
    | (have j0 := eq6366 (σ x)
       grind)
    | exact resolve eq6366 eq359098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6366 eq359098
  have eq1680563 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq1680542
  have eq1680579 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq1680563
       have r₂ := eq436500
       grind)
    | exact resolve eq1680563 eq436500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436500 eq1680563
  have eq1680592 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1680579 eq688364
    | exact resolve eq688364 eq1680579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688364 eq1680579
  have eq1680721 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq1680592 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1680592
  have eq1680735 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1680721 x
       have i₂ := eq14 sF1 x
       grind)
    | exact superpose eq14 eq1680721
    | exact resolve eq1680721 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1680721
  have eq1680737 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq1680735
       have r₂ := eq28
       grind)
    | exact resolve eq1680735 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1680735
  have eq1681432 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op X0 (M.op X0 (σ (M.op x y))))) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq1680737 eq697896
    | exact resolve eq697896 eq1680737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697896 eq1680737
  have eq1681841 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op X0 (M.op X0 (σ (M.op x y))))) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq1681432 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1681432
  have eq1682291 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1681841 x
       have i₂ := eq14521 x sF1
       grind)
    | exact superpose eq14521 eq1681841
    | exact resolve eq1681841 eq14521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14521 eq1681841
  have eq1682533 : x = y := by
    first
    | (have r₁ := eq1682291
       have r₂ := eq28
       grind)
    | exact resolve eq1682291 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1682291
  have eq1682633 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1682533
       grind)
    | exact superpose eq1682533 eq19
    | exact resolve eq19 eq1682533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1682634 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1682533
       grind)
    | exact superpose eq1682533 eq25
    | exact resolve eq25 eq1682533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1682533
  have eq1683765 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1682634
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1682634
    | exact resolve eq1682634 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1682634
  have eq1684097 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1683765 eq27
    | exact resolve eq27 eq1683765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1683765
  have eq1686342 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1684097 eq69
    | exact resolve eq69 eq1684097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq1684097
  have eq1686535 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1686342
       have i₂ := eq1682633
       grind)
    | exact superpose eq1682633 eq1686342
    | exact resolve eq1686342 eq1682633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1682633 eq1686342
  have eq1686669 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1686535 eq15
    | exact resolve eq15 eq1686535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1686535
  have eq1687545 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1686669
    | exact resolve eq1686669 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1686669
  have eq1687788 : False := by grind
  exact eq1687788

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyy_pxy_y_pxy_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq9 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
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
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq35 (τ X0)
       grind)
    | exact superpose eq35 eq18
    | exact resolve eq18 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq40 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq42 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq37
    | exact resolve eq37 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq44 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq40
    | exact resolve eq40 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
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
  clear eq22
  have eq62 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X0 X1) = (M.op X1 X2) ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq14 X0 X1
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq14
    | (have j0 := eq14 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
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
  have eq89 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq91 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq90 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq94 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq95 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq94 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq96 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq89 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq89 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq89 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq89 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq101 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq91 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq91 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq91 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq102 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (M.op X2 X1) = (k X2 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq79 X0 X1 X2
       have j1 := eq12 X2 X1
       grind)
    | (have r₁ := eq79 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq79 X0 X0 X2
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq79 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq108 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X0 X1) = (M.op X1 X2) ∨ (M.op X2 X1) = (k X2 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq62 X0 X1 X2
       have j1 := eq12 X2 X1
       grind)
    | (have r₁ := eq62 X1 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq62 X0 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq62 X1 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq62 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq114 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X2 X1) = (k X2 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq108 X0 X1 X2
       have j1 := eq102 X2 X1 X2
       grind)
    | (have r₁ := eq108 X0 X2 X2
       have r₂ := eq102 X0 X2 X2
       grind)
    | (have r₁ := eq108 X1 X1 X0
       have r₂ := eq102 X0 X1 X1
       grind)
    | (have r₁ := eq108 X0 X1 X2
       have r₂ := eq102 X0 X1 X2
       grind)
    | exact resolve eq108 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq108
  have eq133 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq101 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq101
    | exact resolve eq101 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq101 X1 (τ X0)
       grind)
    | exact superpose eq101 eq17
    | (have j1 := eq101 X1 (τ X0)
       grind)
    | exact resolve eq17 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq139 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq101 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq163 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq95 (σ X1) (σ X0)
       grind)
    | exact superpose eq95 eq15
    | (have j1 := eq95 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq163 X0 X1
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq163
    | (have j0 := eq163 X0 X1
       grind)
    | exact resolve eq163 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq199 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq10
    | exact resolve eq10 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) ≠ (M.op X1 (M.op X2 (M.op (M.op X0 X1) X1))) ∨ (M.op (M.op X0 X1) X1) = (k (M.op X2 (M.op (M.op X0 X1) X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq96 X0 (M.op X1 (M.op (M.op X2 X0) X0))
       have i₂ := eq24 X0 X1 X2
       grind)
    | exact superpose eq24 eq96
    | exact resolve eq96 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq321 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X0 X2 X0 X1
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq395 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq321 X1 x X3
       have i₂ := eq321 X1 x X0
       grind)
    | exact superpose eq321 eq321
    | exact resolve eq321 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq405 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 x
       have i₂ := eq321 X1 x X0
       grind)
    | exact superpose eq321 eq9
    | exact resolve eq9 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X0 (M.op X2 X0) X2
       have i₂ := eq321 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq321 eq24
    | exact resolve eq24 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq423 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq412 X0 X1 X2
       have i₂ := eq24 X0 X0 X1
       grind)
    | exact superpose eq24 eq412
    | exact resolve eq412 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq458 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq405 X0 (M.op X0 X0)
       have i₂ := eq405 X0 X0
       grind)
    | exact superpose eq405 eq405
    | exact resolve eq405 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq465 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (M.op X0 (M.op X0 X1)) X1 X1
       have i₂ := eq405 X0 X1
       grind)
    | exact superpose eq405 eq24
    | exact resolve eq24 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq465 X1 X0 X2
       have i₂ := eq405 X0 X1
       grind)
    | exact superpose eq405 eq465
    | exact resolve eq465 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq523 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1 X0
       have i₂ := eq458 X0
       grind)
    | exact superpose eq458 eq24
    | exact resolve eq24 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq524 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq458 X0
       grind)
    | exact superpose eq458 eq9
    | exact resolve eq9 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq537 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq405 (M.op X0 X0) X0
       have i₂ := eq458 X0
       grind)
    | exact superpose eq458 eq405
    | exact resolve eq405 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq683 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op X2 (σ X1)) ∨ (M.op X2 (σ X1)) = (k X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq114 (σ X0) (σ X1) X2
       grind)
    | exact superpose eq114 eq15
    | (have j1 := eq114 (σ X0) (σ X1) X2
       grind)
    | exact resolve eq15 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq744 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq405 X1 (M.op X1 (M.op X0 X0))
       have i₂ := eq524 X0 X1
       grind)
    | exact superpose eq524 eq405
    | exact resolve eq405 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq813 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq395 X1 (M.op X2 (M.op X0 X0)) X2
       have i₂ := eq524 X0 X2
       grind)
    | exact superpose eq524 eq395
    | exact resolve eq395 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq814 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq395 X1 (M.op X2 (M.op X2 X0)) X0
       have i₂ := eq405 X2 X0
       grind)
    | exact superpose eq405 eq395
    | exact resolve eq395 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq817 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X3 X1))) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq395 X2 (M.op X3 X1) X3
       have i₂ := eq395 X3 X1 X0
       grind)
    | (have i₁ := eq395 X2 (M.op X3 X1) X3
       have i₂ := eq395 X0 X1 X3
       grind)
    | exact superpose eq395 eq395
    | exact resolve eq395 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq997 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X2 X0))) = (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op X2 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq423 (M.op X2 (M.op X2 X0)) X0 X1
       have i₂ := eq405 X2 X0
       grind)
    | exact superpose eq405 eq423
    | exact resolve eq423 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1054 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq458 X1
       have i₂ := eq423 X1 X0 X1
       grind)
    | (have i₁ := eq458 X1
       have i₂ := eq423 X1 X1 X0
       grind)
    | exact superpose eq423 eq458
    | exact resolve eq458 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423 eq458
  have eq1093 : ∀ X0 X2 : G, (M.op X0 (M.op X2 (M.op X2 X0))) = (M.op (M.op X2 (M.op X2 X0)) (M.op X2 (M.op X2 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq997 X0 x X2
       have i₂ := eq1054 x (M.op X2 (M.op X2 X0))
       grind)
    | exact superpose eq1054 eq997
    | exact resolve eq997 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997
  have eq1117 : ∀ X0 X2 : G, (M.op (M.op X2 (M.op X2 X0)) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq1093 X0 X2
       have i₂ := eq405 X2 X0
       grind)
    | exact superpose eq405 eq1093
    | exact resolve eq1093 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq1376 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq469 (M.op X1 (M.op X0 X0)) X2 X1
       have i₂ := eq524 X0 X1
       grind)
    | exact superpose eq524 eq469
    | exact resolve eq469 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1501 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1376 X0 X1 x
       have i₂ := eq813 X0 x X1
       grind)
    | exact superpose eq813 eq1376
    | exact resolve eq1376 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813 eq1376
  have eq1604 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq523 X1 X1
       have i₂ := eq395 X1 X1 X0
       grind)
    | (have i₁ := eq523 X1 X1
       have i₂ := eq395 X0 X1 X1
       grind)
    | exact superpose eq395 eq523
    | exact resolve eq523 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq1745 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq537 (σ X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq537
    | exact resolve eq537 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1746 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq537 (τ X0)
       have i₂ := eq199 X0
       grind)
    | exact superpose eq199 eq537
    | exact resolve eq537 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq1795 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1746 X0
       have i₂ := eq199 (M.op X0 X0)
       grind)
    | exact superpose eq199 eq1746
    | exact resolve eq1746 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq1746
  have eq1796 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1745 X0
       have i₂ := eq42 (M.op X0 X0)
       grind)
    | exact superpose eq42 eq1745
    | exact resolve eq1745 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1745
  have eq1810 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 (M.op (M.op X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq1795 X0
       have i₂ := eq1501 X0 (M.op X0 X0)
       grind)
    | exact superpose eq1501 eq1795
    | exact resolve eq1795 eq1501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1795
  have eq1811 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op (M.op X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq1796 X0
       have i₂ := eq1501 X0 (M.op X0 X0)
       grind)
    | exact superpose eq1501 eq1796
    | exact resolve eq1796 eq1501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796
  have eq1824 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1810 X0
       have i₂ := eq1054 X0 X0
       grind)
    | exact superpose eq1054 eq1810
    | exact resolve eq1810 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1810
  have eq1825 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1811 X0
       have i₂ := eq1054 X0 X0
       grind)
    | exact superpose eq1054 eq1811
    | exact resolve eq1811 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1811
  have eq3892 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 (M.op X1 X1)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1054 X1 (M.op X0 X1)
       have i₂ := eq1501 X1 X0
       grind)
    | (have i₁ := eq1054 X1 (M.op X0 X0)
       have i₂ := eq1501 X0 X1
       grind)
    | exact superpose eq1501 eq1054
    | exact resolve eq1054 eq1501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3894 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq469 X1 X0 X0
       have i₂ := eq1501 (M.op X0 X1) X0
       grind)
    | exact superpose eq1501 eq469
    | exact resolve eq469 eq1501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq3899 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3892 X0 X1
       have i₂ := eq744 X1 X0
       grind)
    | exact superpose eq744 eq3892
    | exact resolve eq3892 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744 eq3892
  have eq4541 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 (M.op X1 (M.op X1 X0))) ∨ (k (M.op X1 (M.op X1 X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X1 (M.op X1 X0)) X0
       have i₂ := eq1604 X1 X0
       grind)
    | exact superpose eq1604 eq13
    | (have j0 := eq13 (M.op X1 (M.op X1 X0)) X0
       grind)
    | (have r₁ := eq13 (M.op X0 (M.op X0 X1)) X1
       have r₂ := eq1604 X0 X1
       grind)
    | exact resolve eq13 eq1604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4563 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k (M.op X1 (M.op X1 X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq139 (M.op X1 (M.op X1 X0)) X0
       have i₂ := eq1604 X1 X0
       grind)
    | exact superpose eq1604 eq139
    | (have j0 := eq139 X0 X0
       grind)
    | exact resolve eq139 eq1604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4590 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 (M.op X1 X0))) ∨ (k (M.op X1 (M.op X1 X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq4541 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4541
  have eq4607 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (M.op X1 (M.op X1 X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4590 X0 X1
       have i₂ := eq405 X1 X0
       grind)
    | exact superpose eq405 eq4590
    | (have j0 := eq4590 X0 X1
       grind)
    | exact resolve eq4590 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4590
  have eq4646 : ∀ X0 X1 : G, (k (M.op X1 (M.op X1 X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq4607 X0 X1
       have j1 := eq4563 X0 X1
       grind)
    | (have r₁ := eq4607 X0 X1
       have r₂ := eq4563 X0 X1
       grind)
    | exact resolve eq4607 eq4563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4563 eq4607
  have eq4756 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (k (M.op X0 X0) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4646 (M.op X1 (M.op X1 X0)) X0
       have i₂ := eq405 X1 X0
       grind)
    | exact superpose eq405 eq4646
    | exact resolve eq4646 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq5917 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq136 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq136
    | exact resolve eq136 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq6008 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5917 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5917
    | (have j0 := eq5917 X0 X1
       grind)
    | exact resolve eq5917 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5917
  have eq6214 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq133 x y
       grind)
    | exact superpose eq133 eq16
    | (have j1 := eq133 x y
       grind)
    | exact resolve eq16 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq7802 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq185 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7803 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq185 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq8017 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1824 X1
       have i₂ := eq395 X1 X1 X0
       grind)
    | (have i₁ := eq1824 X1
       have i₂ := eq395 X0 X1 X1
       grind)
    | exact superpose eq395 eq1824
    | exact resolve eq1824 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1824
  have eq8578 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1825 X1
       have i₂ := eq395 X1 X1 X0
       grind)
    | (have i₁ := eq1825 X1
       have i₂ := eq395 X0 X1 X1
       grind)
    | exact superpose eq395 eq1825
    | exact resolve eq1825 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1825
  have eq9740 : ∀ X0 X1 : G, (M.op X0 (τ (M.op X1 (M.op X1 (σ X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8017 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8017
    | exact resolve eq8017 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8017
  have eq10761 : ∀ X0 X1 X2 : G, (M.op X0 (τ (M.op X1 (M.op X1 (σ X0))))) = (M.op (M.op X2 (M.op X0 (τ (M.op X1 (M.op X1 (σ X0)))))) (τ (M.op X1 (M.op X1 (σ X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (τ (M.op X1 (M.op X1 (σ X0)))) X1 X0
       have i₂ := eq9740 X0 X1
       grind)
    | exact superpose eq9740 eq24
    | exact resolve eq24 eq9740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq10796 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (τ (M.op X1 (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3894 X0 (τ (M.op X1 (M.op X1 (σ X0))))
       have i₂ := eq9740 X0 X1
       grind)
    | exact superpose eq9740 eq3894
    | exact resolve eq3894 eq9740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3894
  have eq10823 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (τ (M.op X1 (M.op X1 (σ X0))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10761 X0 X1 X2
       have i₂ := eq9740 X0 X1
       grind)
    | exact superpose eq9740 eq10761
    | exact resolve eq10761 eq9740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10761
  have eq11219 : ∀ X0 X1 : G, (M.op (σ (M.op X1 (M.op X1 X0))) (σ X0)) = (M.op (σ X0) (M.op (σ (M.op X1 (M.op X1 X0))) (σ (M.op X1 (M.op X1 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1501 (σ (M.op X1 (M.op X1 X0))) (σ X0)
       have i₂ := eq8578 X1 X0
       grind)
    | exact superpose eq8578 eq1501
    | exact resolve eq1501 eq8578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8578
  have eq11232 : ∀ X0 X1 : G, (M.op (σ (M.op X1 (M.op X1 X0))) (σ X0)) = (M.op (σ X0) (σ (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq11219 X0 X1
       have i₂ := eq42 (M.op X1 (M.op X1 X0))
       grind)
    | exact superpose eq42 eq11219
    | exact resolve eq11219 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11219
  have eq11307 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X1 (M.op X1 X0))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11232 X0 X1
       have i₂ := eq1117 X0 X1
       grind)
    | exact superpose eq1117 eq11232
    | exact resolve eq11232 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11232
  have eq11353 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X1 (M.op X1 X0))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11307 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq11307
    | exact resolve eq11307 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11307
  have eq16440 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq814 X2 X1 X1
       have i₂ := eq395 X1 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq814 X2 X1 X1
       have i₂ := eq395 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq395 eq814
    | exact resolve eq814 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16535 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2)))) ≠ (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2)))) ∨ (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2)))) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq96 X0 X0
       have i₂ := eq814 X0 X1 X2
       grind)
    | exact superpose eq814 eq96
    | exact resolve eq96 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq16713 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2)))) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq16535 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16535
  have eq18871 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ X0) (σ y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq683 X0 y (σ x)
       grind)
    | (have i₁ := eq16
       have i₂ := eq683 x y x
       grind)
    | exact superpose eq683 eq16
    | (have j1 := eq683 X0 y (σ x)
       grind)
    | exact resolve eq16 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq18923 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ X0) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq18871 X0
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq18871
    | (have j0 := eq18871 X0
       grind)
    | exact resolve eq18871 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18871
  have eq21504 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16440 X0 (M.op X2 (M.op X2 X0)) (M.op X2 (M.op X2 X0))
       have i₂ := eq1117 X0 X2
       grind)
    | exact superpose eq1117 eq16440
    | exact resolve eq16440 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117
  have eq21773 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = (M.op X0 (M.op X1 (M.op X1 (M.op X0 (σ X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42 X2
       have i₂ := eq16440 X1 X0 (σ X2)
       grind)
    | exact superpose eq16440 eq42
    | exact resolve eq42 eq16440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq16440
  have eq23424 : ∀ X0 X1 X2 : G, (τ (M.op X0 (M.op X0 (M.op X1 (M.op X1 (σ X2)))))) = (k X2 (τ (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X2 (σ X2)
       have i₂ := eq16713 X0 X1 (σ X2)
       grind)
    | exact superpose eq16713 eq30
    | exact resolve eq30 eq16713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq16713
  have eq23430 : ∀ X0 X1 X2 : G, (k X2 X2) = (τ (M.op X0 (M.op X0 (M.op X1 (M.op X1 (σ X2)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23424 X0 X1 X2
       have i₂ := eq10 X2
       grind)
    | exact superpose eq10 eq23424
    | exact resolve eq23424 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23424
  have eq24140 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op X2 (M.op X2 X0))) ≠ (M.op (M.op X2 (M.op X2 X0)) (M.op X0 X0)) ∨ (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op X2 (M.op X2 X0))) = (k (M.op X0 X0) (M.op X2 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq270 X0 (M.op X2 (M.op X2 X0)) (M.op X0 (M.op X2 (M.op X2 X0)))
       have i₂ := eq814 X0 (M.op X0 (M.op X2 (M.op X2 X0))) X2
       grind)
    | exact superpose eq814 eq270
    | exact resolve eq270 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq814
  have eq24214 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op X2 (M.op X2 X0))) ≠ (M.op X0 (M.op (M.op X2 (M.op X2 X0)) X0)) ∨ (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op X2 (M.op X2 X0))) = (k (M.op X0 X0) (M.op X2 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24140 X0 X1 X2
       have i₂ := eq1501 X0 (M.op X2 (M.op X2 X0))
       grind)
    | exact superpose eq1501 eq24140
    | (have j0 := eq24140 X0 X1 X2
       grind)
    | exact resolve eq24140 eq1501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1501 eq24140
  have eq24290 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op X2 (M.op X2 X0))) ∨ (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op X2 (M.op X2 X0))) = (k (M.op X0 X0) (M.op X2 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24214 X0 X1 X2
       have i₂ := eq1604 X2 X0
       grind)
    | exact superpose eq1604 eq24214
    | (have j0 := eq24214 X0 X1 X2
       grind)
    | exact resolve eq24214 eq1604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1604 eq24214
  have eq24359 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op (M.op X2 (M.op X2 X0)) (M.op X2 (M.op X2 X0))) ∨ (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op X2 (M.op X2 X0))) = (k (M.op X0 X0) (M.op X2 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24290 X0 X1 X2
       have i₂ := eq1054 X1 (M.op X2 (M.op X2 X0))
       grind)
    | exact superpose eq1054 eq24290
    | (have j0 := eq24290 X0 X1 X2
       grind)
    | exact resolve eq24290 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24290
  have eq24397 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op X2 (M.op X2 X0))) = (k (M.op X0 X0) (M.op X2 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24359 X0 X1 X2
       have i₂ := eq21504 X0 X2 X2
       grind)
    | exact superpose eq21504 eq24359
    | (have j0 := eq24359 X0 X1 X2
       grind)
    | exact resolve eq24359 eq21504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24359
  have eq24429 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op X2 (M.op X2 X0))) ∨ (M.op X0 (M.op X0 X0)) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24397 X0 X1 X2
       have i₂ := eq4756 X0 X2
       grind)
    | exact superpose eq4756 eq24397
    | (have j0 := eq24397 X0 X1 X2
       grind)
    | exact resolve eq24397 eq4756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4756 eq24397
  have eq24454 : ∀ X0 X2 : G, (M.op X2 (M.op X2 X0)) = (M.op (M.op X2 (M.op X2 X0)) (M.op X2 (M.op X2 X0))) ∨ (M.op X0 (M.op X0 X0)) ≠ X0 := by
    intro X0 X2
    first
    | (have i₁ := eq24429 X0 x X2
       have i₂ := eq1054 x (M.op X2 (M.op X2 X0))
       grind)
    | exact superpose eq1054 eq24429
    | (have j0 := eq24429 X0 x X2
       grind)
    | exact resolve eq24429 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054 eq24429
  have eq24470 : ∀ X0 X2 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (M.op X2 (M.op X2 X0)) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq24454 X0 X2
       have i₂ := eq21504 X0 X2 X2
       grind)
    | exact superpose eq21504 eq24454
    | (have j0 := eq24454 X0 X2
       grind)
    | exact resolve eq24454 eq21504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21504 eq24454
  have eq83604 : ∀ X0 X1 : G, (M.op X1 (τ (τ (M.op X0 (M.op X0 (σ (σ X1))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9740 X1 (σ X1)
       have i₂ := eq10796 (σ X1) X0
       grind)
    | exact superpose eq10796 eq9740
    | exact resolve eq9740 eq10796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9740
  have eq86021 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (τ (τ (M.op X0 (M.op X0 (σ (σ X1))))))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10823 X1 (σ X1) X2
       have i₂ := eq10796 (σ X1) X0
       grind)
    | exact superpose eq10796 eq10823
    | exact resolve eq10823 eq10796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10796 eq10823
  have eq130302 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ X1 ∨ (M.op X2 (M.op X2 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24470 X1 X2
       have i₂ := eq395 X1 X1 X0
       grind)
    | (have i₁ := eq24470 X1 X2
       have i₂ := eq395 X0 X1 X1
       grind)
    | exact superpose eq395 eq24470
    | (have j0 := eq24470 X1 X2
       grind)
    | exact resolve eq24470 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395 eq24470
  have eq242096 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq6214
       have i₂ := eq95 y x
       grind)
    | exact superpose eq95 eq6214
    | (have j1 := eq95 y x
       grind)
    | exact resolve eq6214 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq242100 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq6214
       have i₂ := eq6008 x y
       grind)
    | exact superpose eq6008 eq6214
    | (have j1 := eq6008 x y
       grind)
    | (have r₁ := eq6214
       have r₂ := eq6008 x y
       grind)
    | exact resolve eq6214 eq6008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6008 eq6214
  have eq242101 : (σ (M.op x y)) = (σ y) ∨ y = (k x y) := by grind
  clear eq242100
  have eq242105 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq242096
  have eq242234 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (τ (τ (M.op X0 (M.op X0 (σ (σ y))))))) ∨ y = (k x y) := by
    intro X0
    first
    | (have i₁ := eq83604 X0 (M.op x y)
       have i₂ := eq242101
       grind)
    | exact superpose eq242101 eq83604
    | exact resolve eq83604 eq242101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83604 eq242101
  have eq242237 : y = (M.op x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq242234 x
       have i₂ := eq86021 x y x
       grind)
    | exact superpose eq86021 eq242234
    | exact resolve eq242234 eq86021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86021 eq242234
  have eq242312 : y = (k x y) := by
    first
    | (have j1 := eq139 x y
       grind)
    | (have r₁ := eq242237
       have r₂ := eq139 x y
       grind)
    | exact resolve eq242237 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq242237
  have eq270569 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op X0 (M.op X4 (M.op X4 X2))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq817 X4 X2 x X0
       have i₂ := eq817 X1 X2 x X0
       grind)
    | (have i₁ := eq817 X0 X1 X0 X0
       have i₂ := eq817 X0 X1 X2 X0
       grind)
    | exact superpose eq817 eq817
    | exact resolve eq817 eq817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq308124 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7802 x y
       have i₂ := eq242312
       grind)
    | exact superpose eq242312 eq7802
    | exact resolve eq7802 eq242312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7802
  have eq310034 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7803 (τ X0) (τ X1)
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq7803
    | (have j0 := eq7803 (τ X0) (τ X1)
       grind)
    | exact resolve eq7803 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq7803
  have eq310197 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq310034 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq310034
    | (have j0 := eq310034 X0 X1
       grind)
    | exact resolve eq310034 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310034
  have eq310264 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq310197 X0 X1
       have i₂ := eq44 X1
       grind)
    | exact superpose eq44 eq310197
    | (have j0 := eq310197 X0 X1
       grind)
    | exact resolve eq310197 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310197
  have eq310311 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq310264 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq310264
    | (have j0 := eq310264 X0 X1
       grind)
    | exact resolve eq310264 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310264
  have eq310346 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq310311 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq310311
    | (have j0 := eq310311 X0 X1
       grind)
    | exact resolve eq310311 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310311
  have eq310370 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq310346 X0 X1
       have i₂ := eq44 X1
       grind)
    | exact superpose eq44 eq310346
    | (have j0 := eq310346 X0 X1
       grind)
    | exact resolve eq310346 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq310346
  have eq310545 : y ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq310370 x y
       have i₂ := eq242312
       grind)
    | exact superpose eq242312 eq310370
    | (have j0 := eq310370 x y
       grind)
    | exact resolve eq310370 eq242312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310370
  have eq421013 : ∀ X0 X1 : G, (k (M.op x y) (M.op x y)) = (τ (M.op X0 (M.op X0 (M.op X1 (M.op X1 (σ y)))))) ∨ (M.op x y) = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq23430 X0 X1 (M.op x y)
       have i₂ := eq242105
       grind)
    | exact superpose eq242105 eq23430
    | exact resolve eq23430 eq242105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242105
  have eq421913 : (k y y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq421013 x x
       have i₂ := eq23430 x x y
       grind)
    | exact superpose eq23430 eq421013
    | exact resolve eq421013 eq23430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23430 eq421013
  have eq422280 : (k y y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq421913
       have i₂ := eq35 (M.op x y)
       grind)
    | exact superpose eq35 eq421913
    | exact resolve eq421913 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421913
  have eq422535 : (k y y) = (M.op x (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq422280
       have i₂ := eq3899 x y
       grind)
    | exact superpose eq3899 eq422280
    | exact resolve eq422280 eq3899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3899 eq422280
  have eq422684 : (M.op y y) = (M.op x (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq422535
       have i₂ := eq35 y
       grind)
    | exact superpose eq35 eq422535
    | exact resolve eq422535 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq422535
  have eq1498337 : ∀ X0 : G, (M.op y y) ≠ (M.op x (M.op y y)) ∨ (M.op y y) = (M.op X0 (M.op X0 (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq130302 x (M.op y y) X0
       have i₂ := eq422684
       grind)
    | exact superpose eq422684 eq130302
    | (have j0 := eq130302 X0 (M.op y y) X0
       grind)
    | exact resolve eq130302 eq422684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130302
  have eq1498380 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq1498337 X0
       grind)
    | (have r₁ := eq1498337 X0
       have r₂ := eq422684
       grind)
    | exact resolve eq1498337 eq422684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422684 eq1498337
  have eq1498529 : y = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq1498380 x
       have i₂ := eq524 y x
       grind)
    | exact superpose eq524 eq1498380
    | exact resolve eq1498380 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524 eq1498380
  have eq1498621 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq1498529
       have r₂ := eq310545
       grind)
    | exact resolve eq1498529 eq310545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310545 eq1498529
  have eq1525156 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op y y)) = (σ (k (M.op X0 (M.op X0 y)) y)) := by
    intro X0
    first
    | (have i₁ := eq18923 (M.op x (M.op x y))
       have i₂ := eq11353 y x
       grind)
    | exact superpose eq11353 eq18923
    | (have j0 := eq18923 x
       grind)
    | exact resolve eq18923 eq11353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11353 eq18923
  have eq1525210 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op y y)) = (σ (k (M.op X0 (M.op X0 y)) y)) := by
    intro X0
    first
    | (have i₁ := eq1525156 X0
       have i₂ := eq1498621
       grind)
    | exact superpose eq1498621 eq1525156
    | (have j0 := eq1525156 X0
       grind)
    | exact resolve eq1525156 eq1498621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1525156
  have eq1525211 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op y y)) = (σ (k (M.op X0 (M.op X0 y)) y)) := by
    intro X0
    first
    | (have j0 := eq1525210 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1525210
  have eq1525412 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op y y)) = (σ (k (M.op X0 (M.op X0 y)) y)) := by
    intro X0
    first
    | (have i₁ := eq1525211 X0
       have i₂ := eq242312
       grind)
    | exact superpose eq242312 eq1525211
    | (have j0 := eq1525211 X0
       grind)
    | exact resolve eq1525211 eq242312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242312 eq1525211
  have eq1525447 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1525412 x
       have i₂ := eq4646 y x
       grind)
    | exact superpose eq4646 eq1525412
    | exact resolve eq1525412 eq4646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4646 eq1525412
  have eq1525468 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1525447
       have r₂ := eq308124
       grind)
    | exact resolve eq1525447 eq308124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308124 eq1525447
  have eq1525602 : ∀ X0 : G, (σ (M.op y y)) = (M.op (σ x) (M.op X0 (M.op X0 (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq21773 (σ x) X0 y
       have i₂ := eq1525468
       grind)
    | exact superpose eq1525468 eq21773
    | exact resolve eq21773 eq1525468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21773
  have eq1525886 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 (σ y)))) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq270569 X0 X1 (σ y) (σ x)
       have i₂ := eq1525468
       grind)
    | exact superpose eq1525468 eq270569
    | exact resolve eq270569 eq1525468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270569
  have eq1525923 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X1 (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1525886 X0 X1
       have i₂ := eq1525468
       grind)
    | exact superpose eq1525468 eq1525886
    | exact resolve eq1525886 eq1525468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1525468 eq1525886
  have eq1526096 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op X0 (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1525602 X0
       have i₂ := eq1498621
       grind)
    | exact superpose eq1498621 eq1525602
    | exact resolve eq1525602 eq1498621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498621 eq1525602
  have eq1526331 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1526096 x
       have i₂ := eq1525923 (σ x) x
       grind)
    | exact superpose eq1525923 eq1526096
    | exact resolve eq1526096 eq1525923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1525923 eq1526096
  have eq1526503 : False := by grind
  exact eq1526503

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq97 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq37 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq100 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq97 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq97 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq97 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq97 X0 X1
       have r₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact resolve eq97 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq847 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq100
  have eq855 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq847 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq1431 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq855 (σ X1) (σ X0)
       grind)
    | exact superpose eq855 eq15
    | exact resolve eq15 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1444 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1431 X0 X1
       have i₂ := eq855 X1 X0
       grind)
    | exact superpose eq855 eq1431
    | exact resolve eq1431 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855 eq1431
  have eq1456 : False := by grind
  exact eq1456

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_y_pxy_Equation723 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law723 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
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
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq14 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq16
    | exact resolve eq16 eq49
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
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
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
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
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
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq82
    | exact resolve eq82 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq84
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq84
    | exact resolve eq84 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq91 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq95 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq91
  have eq96 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq95
  have eq526 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq56
    | exact resolve eq56 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq649 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X0 X2 X0 X1
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq697 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 X1
       have i₂ := eq45 X1
       grind)
    | exact superpose eq45 eq73
    | (have j0 := eq73 X0 X1
       grind)
    | exact resolve eq73 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq735 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq697 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq697
    | (have j0 := eq697 x X0
       grind)
    | exact resolve eq697 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq839 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq649 X1 x X3
       have i₂ := eq649 X1 x X0
       grind)
    | exact superpose eq649 eq649
    | exact resolve eq649 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq851 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 x
       have i₂ := eq649 X1 x X0
       grind)
    | exact superpose eq649 eq14
    | exact resolve eq14 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq860 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X0 (M.op X2 X0) X2
       have i₂ := eq649 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq649 eq56
    | exact resolve eq56 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq865 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq860 X0 X1 X2
       have i₂ := eq56 X0 X0 X1
       grind)
    | exact superpose eq56 eq860
    | exact resolve eq860 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860
  have eq880 : y = (M.op y (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq851 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq851
    | (have j0 := eq851 x y
       grind)
    | exact resolve eq851 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq881 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq851
    | (have j0 := eq851 (σ x) (σ y)
       grind)
    | exact resolve eq851 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq886 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq851 X0 (M.op X0 X0)
       have i₂ := eq851 X0 X0
       grind)
    | exact superpose eq851 eq851
    | exact resolve eq851 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq899 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op X0 (M.op y (M.op x (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq880 eq14
    | exact resolve eq14 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq901 : ∀ X0 : G, (M.op y (M.op x (M.op x y))) = (M.op (M.op X0 (M.op y (M.op x (M.op x y)))) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq880 eq56
    | exact resolve eq56 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq905 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq880 eq901
    | exact resolve eq901 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq907 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq880 eq899
    | exact resolve eq899 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq910 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y))))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq881 eq56
    | exact resolve eq56 eq881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq914 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq881 eq910
    | exact resolve eq910 eq881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881 eq910
  have eq1059 : y = (M.op (M.op x y) (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq905 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq905
    | (have j0 := eq905 x
       grind)
    | exact resolve eq905 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq1480 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq880 eq839
    | exact resolve eq839 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1701 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op X0 y) y) := by
    intro X0
    first
    | (have i₁ := eq865 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq865
    | (have j0 := eq865 y X0 x
       grind)
    | exact resolve eq865 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1709 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq865 X0 X1 X0
       have i₂ := eq886 X0
       grind)
    | exact superpose eq886 eq865
    | exact resolve eq865 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq1834 : (M.op (M.op x y) y) = (M.op y y) := by
    first
    | (have i₁ := eq1701 y
       have i₂ := eq886 y
       grind)
    | exact superpose eq886 eq1701
    | exact resolve eq1701 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886 eq1701
  have eq1867 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op y y)) := by
    first
    | exact superpose eq1834 eq907
    | exact resolve eq907 eq1834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907 eq1834
  have eq2203 : (M.op y (M.op x (M.op x y))) = (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) := by
    first
    | exact superpose eq880 eq1709
    | exact resolve eq1709 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2265 : y = (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) := by
    first
    | exact superpose eq880 eq2203
    | exact resolve eq2203 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880 eq2203
  have eq3535 : ∀ X0 : G, (M.op y y) = (M.op x (M.op X0 (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq1480 x
       have i₂ := eq839 x sF0 x
       grind)
    | (have i₁ := eq1480 x
       have i₂ := eq839 X0 sF0 x
       grind)
    | exact superpose eq839 eq1480
    | exact resolve eq1480 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839 eq1480
  have eq3894 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ X0))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq526 X0 (σ (M.op X0 X0))
       have i₂ := eq649 (σ X0) X1 (σ (M.op X0 X0))
       grind)
    | exact superpose eq649 eq526
    | exact resolve eq526 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526 eq649
  have eq3967 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (M.op X1 (σ X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3894 X0 X1
       have i₂ := eq56 (σ X0) (σ X0) X1
       grind)
    | exact superpose eq56 eq3894
    | exact resolve eq3894 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq3894
  have eq3982 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3967 X0 x
       have i₂ := eq1709 (σ X0) x
       grind)
    | exact superpose eq1709 eq3967
    | exact resolve eq3967 eq1709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1709 eq3967
  have eq3985 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3982 X0
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq3982
    | exact resolve eq3982 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq3982
  have eq5116 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq735 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq735
    | (have j0 := eq735 y
       grind)
    | exact resolve eq735 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq5142 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5116
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq5116
    | exact resolve eq5116 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5116
  have eq5161 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq5142
    | exact resolve eq5142 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5142
  have eq5171 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5161
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq5161
    | exact resolve eq5161 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5161
  have eq5177 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq5171
    | exact resolve eq5171 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5171
  have eq15641 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq85 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15642 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq15641
    | exact resolve eq15641 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15641
  have eq15650 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq15642
       have r₂ := eq28
       grind)
    | exact resolve eq15642 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15642
  have eq15653 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq15650
    | exact resolve eq15650 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15650
  have eq15671 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (σ y) = (k X0 (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq15653 eq12
    | (have j0 := eq12 (σ y) X0
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq15653
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq15653
       grind)
    | exact resolve eq12 eq15653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15653
  have eq585476 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq15671
    | (have j0 := eq15671 (σ x)
       grind)
    | (have r₁ := eq15671 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq15671 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15671
  have eq585478 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq585476
  have eq585479 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq585478
  have eq585550 : (τ (σ y)) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq585479 eq60
    | exact resolve eq60 eq585479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq585551 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq585479 eq85
    | exact resolve eq85 eq585479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq585479
  have eq585659 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq585551
  have eq585673 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | exact superpose eq30 eq585550
    | exact resolve eq585550 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585550
  have eq585682 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq585659
       grind)
    | exact superpose eq585659 eq96
    | exact resolve eq96 eq585659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585740 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3985 y
       have i₂ := eq585659
       grind)
    | exact superpose eq585659 eq3985
    | exact resolve eq3985 eq585659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3985 eq585659
  have eq585855 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq585740
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq585740
    | exact resolve eq585740 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585740
  have eq585877 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq585682
    | exact resolve eq585682 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585682
  have eq585896 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq585855
    | exact resolve eq585855 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585855
  have eq586026 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq585877 eq914
    | exact resolve eq914 eq585877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914
  have eq586618 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq1867
       have i₂ := eq585673
       grind)
    | exact superpose eq585673 eq1867
    | exact resolve eq1867 eq585673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1867 eq585673
  have eq615159 : (M.op y y) = (M.op x (M.op (M.op x y) (M.op x (M.op x y)))) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | exact superpose eq586618 eq3535
    | exact resolve eq3535 eq586618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3535 eq586618
  have eq615501 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | exact superpose eq1059 eq615159
    | exact resolve eq615159 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059 eq615159
  have eq615537 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq615501
       have r₂ := eq12 x y
       grind)
    | exact resolve eq615501 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615501
  have eq615585 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq615537
       grind)
    | exact superpose eq615537 eq49
    | exact resolve eq49 eq615537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq615537
  have eq615722 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq615585
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq615585
    | exact resolve eq615585 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615585
  have eq615792 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq615722 eq5177
    | exact resolve eq5177 eq615722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5177 eq615722
  have eq615896 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq615792
  have eq616560 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq615896 eq585877
    | exact resolve eq585877 eq615896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585877
  have eq616689 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq616560
  have eq616762 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq616689
       have r₂ := eq28
       grind)
    | exact resolve eq616689 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616689
  have eq617535 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq616762 eq586026
    | exact resolve eq586026 eq616762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586026
  have eq617538 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq617535
  have eq618242 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq617538
    | exact resolve eq617538 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617538
  have eq621779 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq616762 eq618242
    | exact resolve eq618242 eq616762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616762 eq618242
  have eq621947 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq621779
  have eq625648 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq621947 eq585896
    | exact resolve eq585896 eq621947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585896 eq621947
  have eq625712 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq625648
  have eq625740 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq625712 eq30
    | exact resolve eq30 eq625712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625712
  have eq625936 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq625740
    | exact resolve eq625740 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625740
  have eq625937 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq625936
  have eq625967 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq625937 eq30
    | exact resolve eq30 eq625937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq627204 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq625967
    | exact resolve eq625967 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq625967
  have eq627376 : y = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq627204 eq2265
    | exact resolve eq2265 eq627204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2265
  have eq628617 : y = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq627376
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq627376
    | exact resolve eq627376 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627376
  have eq631314 : y = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq627204 eq628617
    | exact resolve eq628617 eq627204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627204 eq628617
  have eq631750 : y = (M.op y y) ∨ x = y := by grind
  clear eq631314
  have eq635803 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq96
       have i₂ := eq631750
       grind)
    | exact superpose eq631750 eq96
    | exact resolve eq96 eq631750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq631750
  have eq636175 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq635803
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq635803
    | exact resolve eq635803 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635803
  have eq637173 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq636175 eq615896
    | exact resolve eq615896 eq636175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615896 eq636175
  have eq637297 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq637173
  have eq650573 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq637297 eq28
    | exact resolve eq28 eq637297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637297
  have eq652592 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq650573
       have r₂ := eq625937
       grind)
    | exact resolve eq650573 eq625937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625937 eq650573
  have eq652924 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq652592 eq30
    | exact resolve eq30 eq652592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq652592
  have eq653127 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq652924
    | exact resolve eq652924 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq652924
  have eq653128 : x = y := by grind
  clear eq653127
  have eq653156 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq653128
       grind)
    | exact superpose eq653128 eq19
    | exact resolve eq19 eq653128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq653157 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq653128
       grind)
    | exact superpose eq653128 eq25
    | exact resolve eq25 eq653128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq653128
  have eq653552 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq653157
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq653157
    | exact resolve eq653157 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq653157
  have eq654768 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq653552 eq27
    | exact resolve eq27 eq653552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq653552
  have eq655268 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq654768 eq68
    | exact resolve eq68 eq654768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq654768
  have eq655396 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq655268
       have i₂ := eq653156
       grind)
    | exact superpose eq653156 eq655268
    | exact resolve eq655268 eq653156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653156 eq655268
  have eq655620 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq655396 eq15
    | exact resolve eq15 eq655396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655396
  have eq656251 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq655620
    | exact resolve eq655620 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq655620
  have eq656404 : False := by grind
  exact eq656404

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyx_pyx_pxx_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
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
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq52 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq55 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq50 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq50 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq50 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq51 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq51 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq51 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq64 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq52 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq52 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq52 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq73 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq57
  have eq74 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       have j1 := eq55 X1 X0
       grind)
    | (have r₁ := eq64 X0 X1
       have r₂ := eq55 X0 X1
       grind)
    | (have r₁ := eq64 X1 X0
       have r₂ := eq55 X0 X1
       grind)
    | exact resolve eq64 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq64
  have eq239 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq244 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq239 X0 X1
       have j1 := eq73 X1 X0
       grind)
    | (have r₁ := eq239 X0 X0
       have r₂ := eq73 X0 X0
       grind)
    | (have r₁ := eq239 X1 X0
       have r₂ := eq73 X0 X1
       grind)
    | exact resolve eq239 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq239
  have eq514 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq244 (σ X1) (σ X0)
       grind)
    | exact superpose eq244 eq15
    | exact resolve eq15 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq521 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq514 X0 X1
       have i₂ := eq244 X1 X0
       grind)
    | exact superpose eq244 eq514
    | exact resolve eq514 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244 eq514
  have eq524 : False := by grind
  exact eq524

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pxy_pyx_pyy_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq9 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq138 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq138 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq138 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq144 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq139 (σ X0)
       grind)
    | exact superpose eq139 eq15
    | exact resolve eq15 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq144 X0
       have i₂ := eq139 X0
       grind)
    | exact superpose eq139 eq144
    | exact resolve eq144 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq144
  have eq204 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  have eq323 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq204 (σ X1) (σ X0)
       grind)
    | exact superpose eq204 eq15
    | (have j1 := eq204 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq323 X0 X1
       have i₂ := eq151 X1
       grind)
    | exact superpose eq151 eq323
    | (have j0 := eq323 X0 X1
       grind)
    | exact resolve eq323 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq1376 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op X4 X3)) = (M.op (M.op X0 (M.op X0 (M.op X1 X1))) (M.op (M.op X2 X2) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 X3 X4 (M.op (M.op X1 X1) (M.op X1 X1)) X2
       have i₂ := eq61 (M.op X1 X1) X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1427 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X4 (M.op X4 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq61 X1 X4 x x
       have i₂ := eq61 X1 X0 x x
       grind)
    | (have i₁ := eq61 X0 X1 x x
       have i₂ := eq61 X0 (M.op x x) x x
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1488 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X4 X4) X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq9 (M.op (M.op X4 X4) X1) X2 x
       have i₂ := eq61 X1 X0 x X4
       grind)
    | (have i₁ := eq9 (M.op (M.op X2 X2) X0) X1 X2
       have i₂ := eq61 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1496 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X2 X2) x
       have i₂ := eq61 X1 X0 X2 x
       grind)
    | (have i₁ := eq9 X0 (M.op X2 X2) X2
       have i₂ := eq61 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq1798 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) (M.op X1 (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1496 X1 X2 (σ X0)
       have i₂ := eq151 X0
       grind)
    | exact superpose eq151 eq1496
    | exact resolve eq1496 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1815 : ∀ X0 X1 X2 X3 : G, (M.op X3 X1) = (M.op (M.op X2 X2) (M.op X3 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1496 X3 (M.op X3 X1) X2
       have i₂ := eq1427 X3 X1 X0
       grind)
    | (have i₁ := eq1496 X3 (M.op X3 X1) X2
       have i₂ := eq1427 X0 X1 X3
       grind)
    | exact superpose eq1427 eq1496
    | exact resolve eq1496 eq1427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1427
  have eq1929 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq334 x y
       grind)
    | exact superpose eq334 eq16
    | (have j1 := eq334 x y
       grind)
    | exact resolve eq16 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq2028 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X1 X1)) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1798 X1 (σ X0) (σ X0)
       have i₂ := eq151 X0
       grind)
    | exact superpose eq151 eq1798
    | exact resolve eq1798 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6943 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X3 (M.op X4 (M.op X4 (M.op X2 (M.op X2 X0)))))) = X0 := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq1488 X4 (M.op X2 (M.op X2 X0)) X3 x
       have i₂ := eq1496 X2 X0 x
       grind)
    | exact superpose eq1496 eq1488
    | exact resolve eq1488 eq1496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488 eq1496
  have eq20864 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq1929
       have i₂ := eq204 y x
       grind)
    | exact superpose eq204 eq1929
    | (have j1 := eq204 y x
       grind)
    | exact resolve eq1929 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq1929
  have eq20865 : (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq20864
  have eq26917 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X0 (M.op X0 (M.op X1 X1))) (M.op (M.op X2 X2) (M.op X3 (M.op X4 (M.op X4 X5)))))) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq6943 X5 X4 X3 X3
       have i₂ := eq1376 X0 X1 X2 (M.op X3 (M.op X4 (M.op X4 X5))) X3
       grind)
    | exact superpose eq1376 eq6943
    | exact resolve eq6943 eq1376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1376 eq6943
  have eq27440 : ∀ X0 X1 X3 X5 : G, (M.op X3 (M.op (M.op X0 (M.op X0 (M.op X1 X1))) (M.op X3 X5))) = X5 := by
    intro X0 X1 X3 X5
    first
    | (have i₁ := eq26917 X0 X1 x X3 x X5
       have i₂ := eq1815 x X5 x X3
       grind)
    | exact superpose eq1815 eq26917
    | exact resolve eq26917 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1815 eq26917
  have eq75920 : ∀ X0 : G, (σ x) = (M.op (σ (M.op X0 X0)) (M.op (σ y) (σ (M.op y y)))) ∨ (M.op y y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq1798 X0 (σ y) (σ x)
       have i₂ := eq20865
       grind)
    | exact superpose eq20865 eq1798
    | exact resolve eq1798 eq20865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1798 eq20865
  have eq75962 : (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq75920 x
       have i₂ := eq2028 y x
       grind)
    | exact superpose eq2028 eq75920
    | exact resolve eq75920 eq2028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2028 eq75920
  have eq76213 : ∀ X0 X1 : G, y = (M.op y (M.op (M.op X0 (M.op X0 (M.op X1 X1))) (M.op y x))) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq27440 X0 X1 y y
       have i₂ := eq75962
       grind)
    | exact superpose eq75962 eq27440
    | exact resolve eq27440 eq75962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75962
  have eq76216 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq76213 x x
       have i₂ := eq27440 x x y x
       grind)
    | (have i₁ := eq76213 x x
       have i₂ := eq27440 x x x (M.op y (M.op (M.op x (M.op x (M.op x x))) (M.op y x)))
       grind)
    | exact superpose eq27440 eq76213
    | exact resolve eq76213 eq27440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27440 eq76213
  have eq76246 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq76216
       grind)
    | exact superpose eq76216 eq10
    | exact resolve eq10 eq76216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76216
  have eq76288 : x = y ∨ x = y := by
    first
    | (have i₁ := eq76246
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq76246
    | exact resolve eq76246 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76246
  have eq76289 : x = y := by grind
  clear eq76288
  have eq76293 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq76289
       grind)
    | exact superpose eq76289 eq16
    | exact resolve eq16 eq76289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76289
  have eq76294 : False := by grind
  exact eq76294

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pyx_pxx_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq9 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq45 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq45 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq48 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
  have eq55 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq48 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq48
    | exact resolve eq48 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq79 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq78 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq85 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq79 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq79 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq96 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq85
  have eq668 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X2 X2) x
       have i₂ := eq23 X1 X0 X2 x
       grind)
    | (have i₁ := eq9 X0 (M.op X2 X2) X2
       have i₂ := eq23 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq859 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq668 X0 X0 X2
       have i₂ := eq96 X0 X1
       grind)
    | (have i₁ := eq668 X0 X1 X2
       have i₂ := eq96 X0 X1
       grind)
    | exact superpose eq96 eq668
    | (have j1 := eq96 X0 X1
       grind)
    | exact resolve eq668 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq914 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq859 X0 X1 x
       have i₂ := eq668 X0 X1 x
       grind)
    | exact superpose eq668 eq859
    | (have j0 := eq859 X0 X1 x
       grind)
    | exact resolve eq859 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668 eq859
  have eq1020 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq914 (τ X0) X1
       grind)
    | exact superpose eq914 eq18
    | (have j1 := eq914 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1022 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq914 (σ X0) (σ X1)
       grind)
    | exact superpose eq914 eq15
    | (have j1 := eq914 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914
  have eq10747 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1020 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1020
    | exact resolve eq1020 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq10813 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10747 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq10747
    | (have j0 := eq10747 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq10747 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10747
  have eq126613 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1022 x y
       grind)
    | exact superpose eq1022 eq16
    | (have j1 := eq1022 x y
       grind)
    | exact resolve eq16 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq128323 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq126613
       have i₂ := eq10813 x y
       grind)
    | exact superpose eq10813 eq126613
    | (have j1 := eq10813 (σ x) (σ y)
       grind)
    | (have r₁ := eq126613
       have r₂ := eq10813 x y
       grind)
    | (have r₁ := eq126613
       have r₂ := eq10813 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq126613
       have r₂ := eq10813 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq126613 eq10813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10813 eq126613
  have eq128324 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq128323
  have eq130645 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq128324
       grind)
    | exact superpose eq128324 eq10
    | exact resolve eq10 eq128324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128324
  have eq130704 : x = y ∨ x = y := by
    first
    | (have i₁ := eq130645
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq130645
    | exact resolve eq130645 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130645
  have eq130705 : x = y := by grind
  clear eq130704
  have eq134511 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq130705
       grind)
    | exact superpose eq130705 eq16
    | exact resolve eq16 eq130705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130705
  have eq134512 : False := by grind
  exact eq134512
