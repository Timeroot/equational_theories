import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_pxx_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) ≠ (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq62 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1070 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1072 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) ≠ (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1422 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
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
  have eq1429 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
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
  have eq1438 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1429 X0 X1
       have j1 := eq1072 X0 X1
       grind)
    | (have r₁ := eq1429 X0 X1
       have r₂ := eq1072 X0 X1
       grind)
    | (have r₁ := eq1429 (τ X1) X1
       have r₂ := eq1072 (τ X1) X1
       grind)
    | exact resolve eq1429 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072 eq1429
  have eq1445 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1422 X0 X1
       have j1 := eq1070 X0 X1
       grind)
    | (have r₁ := eq1422 X0 X1
       have r₂ := eq1070 X0 X1
       grind)
    | (have r₁ := eq1422 X1 X1
       have r₂ := eq1070 X1 X1
       grind)
    | exact resolve eq1422 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422
  have eq1460 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1438 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1438
    | exact resolve eq1438 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438
  have eq1492 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1460 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1460
    | (have j0 := eq1460 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq1460 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1460
  have eq1730 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1445 x y
       grind)
    | exact superpose eq1445 eq16
    | (have j1 := eq1445 x y
       grind)
    | exact resolve eq16 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445
  have eq1756 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1730
       have i₂ := eq1492 y x
       grind)
    | exact superpose eq1492 eq1730
    | (have j1 := eq1492 (σ x) (σ y)
       grind)
    | (have r₁ := eq1730
       have r₂ := eq1492 y x
       grind)
    | (have r₁ := eq1730
       have r₂ := eq1492 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1730
       have r₂ := eq1492 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1730 eq1492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1492 eq1730
  have eq1757 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1756
  have eq1761 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1757
       grind)
    | exact superpose eq1757 eq16
    | exact resolve eq16 eq1757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1757
  have eq7584 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq1070 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070
  have eq7595 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7584 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7584
    | exact resolve eq7584 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7606 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X1 (σ X0)
       have i₂ := eq7584 X0
       grind)
    | exact superpose eq7584 eq65
    | exact resolve eq65 eq7584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq7664 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq7595 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq7595
    | exact resolve eq7595 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq7595
  have eq7668 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq7664 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7664
    | exact resolve eq7664 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7664
  have eq7831 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq7606 X0 X1
       have i₂ := eq7668 X0
       grind)
    | exact superpose eq7668 eq7606
    | exact resolve eq7606 eq7668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7606
  have eq8128 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op X1 (M.op (M.op X1 (σ (M.op X0 X0))) (M.op X1 (σ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (M.op X1 (σ (M.op X0 X0))) X1
       have i₂ := eq7831 X0 X1
       grind)
    | exact superpose eq7831 eq62
    | exact resolve eq62 eq7831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq7831
  have eq8176 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8128 X0 x
       have i₂ := eq9 (σ (M.op X0 X0)) x
       grind)
    | exact superpose eq9 eq8128
    | exact resolve eq8128 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8128
  have eq8315 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1761
       have i₂ := eq8176 x
       grind)
    | exact superpose eq8176 eq1761
    | (have r₁ := eq1761
       have r₂ := eq8176 x
       grind)
    | exact resolve eq1761 eq8176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1761 eq8176
  have eq8372 : (σ x) = (σ y) := by grind
  clear eq8315
  have eq8427 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8372
       grind)
    | exact superpose eq8372 eq16
    | exact resolve eq16 eq8372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8428 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq8372
       grind)
    | exact superpose eq8372 eq10
    | exact resolve eq10 eq8372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8372
  have eq8475 : x = y := by
    first
    | (have i₁ := eq8428
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8428
    | exact resolve eq8428 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8428
  have eq8476 : (σ (M.op x y)) ≠ (σ (k x x)) := by
    first
    | (have i₁ := eq8427
       have i₂ := eq7584 x
       grind)
    | exact superpose eq7584 eq8427
    | exact resolve eq8427 eq7584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7584 eq8427
  have eq8481 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8476
       have i₂ := eq7668 x
       grind)
    | exact superpose eq7668 eq8476
    | exact resolve eq8476 eq7668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7668 eq8476
  have eq8485 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8481
       have i₂ := eq8475
       grind)
    | exact superpose eq8475 eq8481
    | exact resolve eq8481 eq8475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8475 eq8481
  have eq8486 : False := by grind
  exact eq8486

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_x_pyx_pxx_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
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
  clear eq24
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq22 eq36
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq88
       have i₂ := eq68 y x
       grind)
    | exact superpose eq68 eq88
    | (have j1 := eq68 y x
       grind)
    | exact resolve eq88 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq93
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq93
    | exact resolve eq93 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq99
    | exact resolve eq99 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq111 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op (M.op (M.op X1 X0) (M.op X1 X0)) X1) = X1 ∨ (k X1 (M.op (M.op X1 X0) (M.op X1 X0))) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op (M.op X1 X0) (M.op X1 X0))
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 (M.op (M.op X1 X0) (M.op X1 X0))
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq326 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq336 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq318 X0 X1
       have i₂ := eq52 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq52 eq318
    | exact resolve eq318 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq341 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq336 X0 X1
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq336
    | exact resolve eq336 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq608 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq100 eq68
    | (have j0 := eq68 (σ y) (σ x)
       grind)
    | exact resolve eq68 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq609 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq608
    | exact resolve eq608 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq612 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq609
       have r₂ := eq27
       grind)
    | exact resolve eq609 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq617 : (σ x) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq612 eq14
    | exact resolve eq14 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq621 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq617 eq52
    | exact resolve eq52 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq626 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq621
       have i₂ := eq14 sF3 sF3
       grind)
    | exact superpose eq14 eq621
    | exact resolve eq621 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq684 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) X1) = X1 ∨ X0 ≠ X1 ∨ (k X1 (M.op (M.op X1 X0) (M.op X1 X0))) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq111 X0 X1
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq111
    | (have j0 := eq111 X0 X1
       grind)
    | (have r₁ := eq111 (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 (M.op X0 X0))
       have r₂ := eq52 X0 X1
       grind)
    | (have r₁ := eq111 (M.op X1 (M.op X0 X0)) (M.op (M.op X1 X0) (M.op X1 X0))
       have r₂ := eq52 X0 X1
       grind)
    | exact resolve eq111 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq685 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op (M.op X1 (M.op X0 X0)) X1) = X1 ∨ (M.op X1 X1) = (k X1 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq684 X0 X1
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq684
    | (have j0 := eq684 X0 X1
       grind)
    | (have r₁ := eq684 (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 (M.op X0 X0))
       have r₂ := eq52 X0 X1
       grind)
    | (have r₁ := eq684 (M.op X1 (M.op X0 X0)) (M.op (M.op X1 X0) (M.op X1 X0))
       have r₂ := eq52 X0 X1
       grind)
    | exact resolve eq684 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq716 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) ∨ (M.op (M.op X0 (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq685 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq5005 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq716 (M.op x x)
       have i₂ := eq326 (M.op x x) x
       grind)
    | exact superpose eq326 eq716
    | exact resolve eq716 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq5038 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5005 X0
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq5005
    | (have j0 := eq5005 X0
       grind)
    | exact resolve eq5005 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq5005
  have eq5043 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq5038 X0
       have j1 := eq13 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq5038 x
       have r₂ := eq13 (M.op x x) x
       grind)
    | exact resolve eq5038 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5038
  have eq10893 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq626 eq5043
    | exact resolve eq5043 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq10913 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq10893
    | exact resolve eq10893 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10893
  have eq10924 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq10913 eq100
    | exact resolve eq100 eq10913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq10913
  have eq10930 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq10924
  have eq10932 : y = (M.op y x) := by
    first
    | (have r₁ := eq10930
       have r₂ := eq27
       grind)
    | exact resolve eq10930 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10930
  have eq10941 : (M.op x x) = (M.op y (M.op y (M.op y (M.op x x)))) := by
    first
    | (have i₁ := eq341 x y
       have i₂ := eq10932
       grind)
    | exact superpose eq10932 eq341
    | exact resolve eq341 eq10932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10947 : (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq10941
       have i₂ := eq326 y x
       grind)
    | exact superpose eq326 eq10941
    | exact resolve eq10941 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10941
  have eq10952 : y = (M.op x x) := by
    first
    | (have i₁ := eq10947
       have i₂ := eq10932
       grind)
    | exact superpose eq10932 eq10947
    | exact resolve eq10947 eq10932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10932 eq10947
  have eq11071 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq5043 x
       have i₂ := eq10952
       grind)
    | exact superpose eq10952 eq5043
    | exact resolve eq5043 eq10952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10952
  have eq11087 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq11071
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11071
    | exact resolve eq11071 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq11071
  have eq11326 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq88
       have i₂ := eq11087
       grind)
    | exact superpose eq11087 eq88
    | exact resolve eq88 eq11087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq11087
  have eq11334 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq11326
    | exact resolve eq11326 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq11326
  have eq11527 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq11334 eq68
    | (have j0 := eq68 (σ y) (σ x)
       grind)
    | exact resolve eq68 eq11334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq11528 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11527
    | exact resolve eq11527 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11527
  have eq11531 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq11528
       have r₂ := eq27
       grind)
    | exact resolve eq11528 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11528
  have eq11563 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ x))))) := by
    first
    | exact superpose eq11531 eq341
    | exact resolve eq341 eq11531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq11569 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq11563
       have i₂ := eq326 sF3 sF2
       grind)
    | exact superpose eq326 eq11563
    | exact resolve eq11563 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326 eq11563
  have eq11573 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11531 eq11569
    | exact resolve eq11569 eq11531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11531 eq11569
  have eq11730 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq11573 eq5043
    | exact resolve eq5043 eq11573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5043 eq11573
  have eq11746 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11334 eq11730
    | exact resolve eq11730 eq11334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11334 eq11730
  have eq11754 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11746
    | exact resolve eq11746 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq11746
  have eq11757 : False := by grind
  exact eq11757

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_pyy_pxy_pyx_pxy_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq19 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq56 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq56 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq56 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq61 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq57 (σ X0)
       grind)
    | exact superpose eq57 eq15
    | exact resolve eq15 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq57 (τ X0)
       grind)
    | exact superpose eq57 eq18
    | exact resolve eq18 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq64
    | exact resolve eq64 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq70 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq61
    | exact resolve eq61 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq73 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq67
    | exact resolve eq67 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq67
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq97 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 X1
       have i₂ := eq70 X1
       grind)
    | exact superpose eq70 eq91
    | (have j0 := eq91 X0 X1
       grind)
    | exact resolve eq91 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq107 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq10
    | exact resolve eq10 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq135 X0 X1
       have i₂ := eq19 (M.op X1 X1) X0
       grind)
    | exact superpose eq19 eq135
    | exact resolve eq135 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq147 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq133 X0 X1
       have i₂ := eq19 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq19 eq133
    | exact resolve eq133 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq149 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq145 X0 X1
       have i₂ := eq19 X1 X1
       grind)
    | exact superpose eq19 eq145
    | exact resolve eq145 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq151 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq147 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq147
    | exact resolve eq147 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq152 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq151 X0 X1
       have i₂ := eq149 X1 X0
       grind)
    | exact superpose eq149 eq151
    | exact resolve eq151 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq151
  have eq153 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq136 X1 (σ X0)
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq136
    | exact resolve eq136 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq136 X1 (τ X0)
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq136
    | exact resolve eq136 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq97
    | exact resolve eq97 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq304 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq271 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq271
    | (have j0 := eq271 X0 X1
       grind)
    | exact resolve eq271 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq271
  have eq314 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq304 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq304 X1 (M.op (τ X1) (τ X1))
       have r₂ := eq12 (σ (M.op (τ X1) (τ X1))) X1
       grind)
    | (have r₁ := eq304 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq304 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq318 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq314 X0 X1
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq314
    | (have j0 := eq314 X0 X1
       grind)
    | exact resolve eq314 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq314
  have eq380 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq152 (M.op X0 X0) X1
       have i₂ := eq136 (M.op X0 X0) X0
       grind)
    | exact superpose eq136 eq152
    | exact resolve eq152 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (M.op X1 (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq152 (τ (M.op X0 X0)) X1
       have i₂ := eq181 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq181 eq152
    | exact resolve eq152 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq397 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X1 (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq383 X0 X1
       have i₂ := eq107 (M.op X0 X0)
       grind)
    | exact superpose eq107 eq383
    | exact resolve eq383 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq383
  have eq400 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq380 X0 X1
       have i₂ := eq19 X0 X0
       grind)
    | exact superpose eq19 eq380
    | exact resolve eq380 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq405 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 X0))) = (M.op X1 (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq397 X0 X1
       have i₂ := eq19 X0 X0
       grind)
    | exact superpose eq19 eq397
    | exact resolve eq397 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq397
  have eq412 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq400 X1 X2
       have i₂ := eq400 X1 X0
       grind)
    | (have i₁ := eq400 X0 X1
       have i₂ := eq400 X0 X0
       grind)
    | exact superpose eq400 eq400
    | exact resolve eq400 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq152 X1 X2
       have i₂ := eq400 X1 X0
       grind)
    | (have i₁ := eq152 X0 X1
       have i₂ := eq400 X0 X0
       grind)
    | exact superpose eq400 eq152
    | exact resolve eq152 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq400
  have eq552 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X2 (σ (M.op X0 X0))))) = (M.op X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq412 X1 (M.op X2 (σ (M.op X0 X0))) X2
       have i₂ := eq153 X0 X2
       grind)
    | exact superpose eq153 eq412
    | exact resolve eq412 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq2064 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq318 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq318
    | exact resolve eq318 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2072 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq318 (σ X1) X0
       grind)
    | exact superpose eq318 eq15
    | (have j1 := eq318 (σ X1) X0
       grind)
    | exact resolve eq15 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq2086 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2072 X0 X1
       have i₂ := eq70 X1
       grind)
    | exact superpose eq70 eq2072
    | (have j0 := eq2072 X0 X1
       grind)
    | exact resolve eq2072 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2072
  have eq2147 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq427 X1 X2 X1
       have i₂ := eq412 X1 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq427 X1 X2 X1
       have i₂ := eq412 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq412 eq427
    | exact resolve eq427 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2172 : ∀ X0 X1 X2 X3 : G, (τ X2) = (M.op X3 (M.op X3 (τ (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq181 X2 X3
       have i₂ := eq427 X1 X2 X0
       grind)
    | exact superpose eq427 eq181
    | exact resolve eq181 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq427
  have eq2531 : ∀ X0 X1 X2 : G, (τ (M.op X0 (M.op X0 X1))) = (M.op X2 (M.op X2 (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq405 X1 X2
       have i₂ := eq412 X1 X1 X0
       grind)
    | (have i₁ := eq405 X1 X2
       have i₂ := eq412 X0 X1 X1
       grind)
    | exact superpose eq412 eq405
    | exact resolve eq405 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq3261 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = (M.op X0 (M.op X1 (M.op X1 (M.op X0 (σ X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 X2
       have i₂ := eq2147 X1 X0 (σ X2)
       grind)
    | exact superpose eq2147 eq70
    | exact resolve eq70 eq2147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2147
  have eq4657 : ∀ X0 X1 X2 X3 : G, (τ (M.op X2 (M.op X0 (M.op X0 X1)))) = (M.op X3 (M.op X3 (τ (M.op X2 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2531 X2 (M.op X2 X1) X3
       have i₂ := eq412 X2 X1 X0
       grind)
    | (have i₁ := eq2531 X2 (M.op X2 X1) X3
       have i₂ := eq412 X0 X1 X2
       grind)
    | exact superpose eq412 eq2531
    | exact resolve eq2531 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412 eq2531
  have eq11518 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq2064 (τ X0) X1
       grind)
    | exact superpose eq2064 eq17
    | (have j1 := eq2064 (τ X0) X1
       grind)
    | exact resolve eq17 eq2064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq2064
  have eq44329 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2086 x y
       grind)
    | exact superpose eq2086 eq16
    | (have j1 := eq2086 x y
       grind)
    | exact resolve eq16 eq2086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2086
  have eq55477 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (τ (M.op X0 (M.op X1 (M.op X1 (M.op X0 (σ X2)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X2 X2)
       have i₂ := eq3261 X0 X1 X2
       grind)
    | exact superpose eq3261 eq10
    | exact resolve eq10 eq3261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3261
  have eq114153 : ∀ X0 X1 X2 X3 : G, (M.op X2 (τ (M.op X0 (M.op X1 (M.op X1 (M.op X0 (σ (M.op X2 X3)))))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X2
       have i₂ := eq55477 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq55477 eq9
    | exact resolve eq9 eq55477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55477
  have eq527592 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op X4 (τ (M.op X2 (M.op X3 (M.op X0 (σ (M.op X1 X1)))))))) = (τ (M.op X2 (M.op X3 (M.op X0 (σ X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq4657 X3 (M.op X3 (M.op X0 (σ (M.op X1 X1)))) X2 X4
       have i₂ := eq552 X1 X3 X0
       grind)
    | exact superpose eq552 eq4657
    | exact resolve eq4657 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552 eq4657
  have eq2067314 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11518 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11518
    | exact resolve eq11518 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11518
  have eq2069470 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2067314 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2067314
    | (have j0 := eq2067314 X0 X1
       grind)
    | exact resolve eq2067314 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2067314
  have eq2092691 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq44329
       have i₂ := eq2069470 x y
       grind)
    | exact superpose eq2069470 eq44329
    | (have j1 := eq2069470 x y
       grind)
    | (have r₁ := eq44329
       have r₂ := eq2069470 x y
       grind)
    | exact resolve eq44329 eq2069470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44329 eq2069470
  have eq2092694 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq2092691
  have eq2092878 : ∀ X0 X1 : G, (τ (σ x)) = (M.op X0 (M.op X0 (τ (M.op X1 (M.op X1 (M.op (σ y) (σ (M.op y y)))))))) ∨ (M.op y y) = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq2172 X1 (σ y) (σ x) X0
       have i₂ := eq2092694
       grind)
    | exact superpose eq2092694 eq2172
    | exact resolve eq2172 eq2092694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2172 eq2092694
  have eq2093472 : ∀ X1 : G, (τ (σ x)) = (τ (M.op X1 (M.op X1 (M.op (σ y) (σ y))))) ∨ (M.op y y) = (M.op y x) := by
    intro X1
    first
    | (have i₁ := eq2092878 x X1
       have i₂ := eq527592 (σ y) y X1 X1 x
       grind)
    | exact superpose eq527592 eq2092878
    | exact resolve eq2092878 eq527592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527592 eq2092878
  have eq2093866 : (τ (σ x)) = (τ (σ y)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq2093472 x
       have i₂ := eq136 x (σ y)
       grind)
    | exact superpose eq136 eq2093472
    | exact resolve eq2093472 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq2093472
  have eq2094190 : y = (τ (σ x)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq2093866
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2093866
    | exact resolve eq2093866 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2093866
  have eq2094365 : x = y ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq2094190
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2094190
    | exact resolve eq2094190 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2094190
  have eq2094466 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2094365
       grind)
    | exact superpose eq2094365 eq16
    | exact resolve eq16 eq2094365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2094365
  have eq2094467 : (M.op y y) = (M.op y x) := by
    first
    | (have r₁ := eq2094466
       have r₂ := eq70 x
       grind)
    | exact resolve eq2094466 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2094466
  have eq2096206 : ∀ X0 X1 : G, y = (M.op y (τ (M.op X0 (M.op X1 (M.op X1 (M.op X0 (σ (M.op y x)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq114153 X0 X1 y y
       have i₂ := eq2094467
       grind)
    | exact superpose eq2094467 eq114153
    | exact resolve eq114153 eq2094467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2094467
  have eq2096296 : x = y := by
    first
    | (have i₁ := eq2096206 x x
       have i₂ := eq114153 x x y x
       grind)
    | exact superpose eq114153 eq2096206
    | exact resolve eq2096206 eq114153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114153 eq2096206
  have eq2097169 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2096296
       grind)
    | exact superpose eq2096296 eq16
    | exact resolve eq16 eq2096296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2096296
  have eq2097172 : False := by grind
  exact eq2097172

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyy_pxx_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
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
  clear eq36
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
  clear eq44
  have eq51 : y = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq75 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq71 sF2
       grind)
    | exact superpose eq71 eq50
    | exact resolve eq50 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq76 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq75
       have i₂ := eq71 x
       grind)
    | exact superpose eq71 eq75
    | exact resolve eq75 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq99 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq100 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq104 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq100
       have i₂ := eq71 sF3
       grind)
    | exact superpose eq71 eq100
    | exact resolve eq100 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq106 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq71 y
       grind)
    | exact superpose eq71 eq104
    | exact resolve eq104 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq104
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq99
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq99 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq129 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq122
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq122
    | exact resolve eq122 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq130 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq129
    | exact resolve eq129 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq131 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq130
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq130
    | exact resolve eq130 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq144 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq106
       grind)
    | exact superpose eq106 eq16
    | exact resolve eq16 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : (M.op y y) = (M.op x (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq387 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq389 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq395 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq387
       have i₂ := eq53 sF4 sF4
       grind)
    | exact superpose eq53 eq387
    | exact resolve eq387 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq397 : (M.op y y) = (M.op x (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq384
       have i₂ := eq53 sF0 sF0
       grind)
    | exact superpose eq53 eq384
    | exact resolve eq384 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq384
  have eq409 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq389 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq389 (M.op X0 X0) X0
       grind)
    | exact superpose eq389 eq389
    | exact resolve eq389 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq873 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq131 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq874 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq873
    | exact resolve eq873 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq877 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq874
       have r₂ := eq28
       grind)
    | exact resolve eq874 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq879 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq877
    | exact resolve eq877 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877
  have eq884 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ x)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq879 eq395
    | exact resolve eq395 eq879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395 eq879
  have eq888 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq884
       have i₂ := eq389 sF2 sF2
       grind)
    | exact superpose eq389 eq884
    | exact resolve eq884 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884
  have eq891 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq888 eq144
    | exact resolve eq144 eq888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq888
  have eq899 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq891
    | exact resolve eq891 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891
  have eq907 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq409 y
       have i₂ := eq899
       grind)
    | exact superpose eq899 eq409
    | exact resolve eq409 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq909 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq907
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq907
    | exact resolve eq907 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907
  have eq910 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq909
  have eq913 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq910 eq30
    | exact resolve eq30 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq910
  have eq937 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq913
    | exact resolve eq913 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq913
  have eq938 : x = (M.op x y) ∨ x = y := by grind
  clear eq937
  have eq992 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq938 eq21
    | exact resolve eq21 eq938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1000 : (M.op y y) = (M.op x (M.op x (M.op x x))) ∨ x = y := by
    first
    | exact superpose eq938 eq397
    | exact resolve eq397 eq938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397 eq938
  have eq1008 : x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1000
       have i₂ := eq389 x x
       grind)
    | exact superpose eq389 eq1000
    | exact resolve eq1000 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389 eq1000
  have eq1014 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq992
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq992
    | exact resolve eq992 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq1052 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq106
       have i₂ := eq1008
       grind)
    | exact superpose eq1008 eq106
    | exact resolve eq106 eq1008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq1008
  have eq1060 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1052
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1052
    | exact resolve eq1052 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052
  have eq1128 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1060 eq409
    | exact resolve eq409 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409 eq1060
  have eq1131 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq1128
    | exact resolve eq1128 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128
  have eq1134 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq1131 eq28
    | exact resolve eq28 eq1131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131
  have eq1142 : x = y := by
    first
    | (have r₁ := eq1134
       have r₂ := eq1014
       grind)
    | exact resolve eq1134 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014 eq1134
  have eq1199 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1142
       grind)
    | exact superpose eq1142 eq19
    | exact resolve eq19 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1200 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1142
       grind)
    | exact superpose eq1142 eq25
    | exact resolve eq25 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1142
  have eq1223 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1200
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1200
    | exact resolve eq1200 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1200
  have eq1226 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1223 eq27
    | exact resolve eq27 eq1223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1223
  have eq1344 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1226 eq76
    | exact resolve eq76 eq1226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq1226
  have eq1353 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1344
       have i₂ := eq1199
       grind)
    | exact superpose eq1199 eq1344
    | exact resolve eq1344 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199 eq1344
  have eq1356 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1353 eq15
    | exact resolve eq15 eq1353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1353
  have eq1383 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1356
    | exact resolve eq1356 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1356
  have eq1387 : False := by grind
  exact eq1387

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyy_pyx_pxy_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq20 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq25 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  have eq31 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
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
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq68 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k (M.op X0 (M.op X1 X1)) (M.op X0 X1)) := by
    intro X0 X1
    grind
  clear eq20
  have eq97 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (σ X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35 (k X1 (τ X0)) X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq35
    | exact resolve eq35 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (σ X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35 X0 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq35
    | exact resolve eq35 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq153 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) X0) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq27 X0
       have i₂ := eq25 (τ X0)
       grind)
    | exact superpose eq25 eq27
    | (have j1 := eq25 (τ X0)
       grind)
    | exact resolve eq27 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq27
  have eq173 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq153 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq153
    | (have j0 := eq153 X0
       grind)
    | exact resolve eq153 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq179 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq173 X0
       have i₂ := eq39 X0 X0
       grind)
    | exact superpose eq39 eq173
    | (have j0 := eq173 X0
       grind)
    | exact resolve eq173 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq173
  have eq242 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq68 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq68 (M.op X0 X0) X0
       grind)
    | exact superpose eq68 eq68
    | exact resolve eq68 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476 : ∀ X0 X1 : G, (k X0 (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq70 X1 (M.op X1 X0)
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq70
    | exact resolve eq70 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq962 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (σ X2)) ≠ (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) ∨ (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k (σ X0) X1) (σ X2)
       have i₂ := eq97 X0 X1 X2
       grind)
    | exact superpose eq97 eq13
    | (have j0 := eq13 (k (σ X0) X1) (σ X2)
       have j1 := eq97 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X2) (k (σ X0) X1)
       have r₂ := eq97 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (σ X2)
       have r₂ := eq97 X0 X1 X2
       grind)
    | exact resolve eq13 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq970 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (σ X2)) ≠ (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) ∨ (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq962 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq971 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op (σ X2) (σ X2)) ∨ (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq970 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq977 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq971 X0 X1 X2
       have i₂ := eq31 X0 X1 X2
       grind)
    | exact superpose eq31 eq971
    | (have j0 := eq971 X0 X1 X2
       grind)
    | exact resolve eq971 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq971
  have eq978 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq977 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq1027 : ∀ X0 X1 X2 : G, (M.op (σ X0) (k X1 (σ X2))) ≠ (M.op (σ X0) (k X1 (σ X2))) ∨ (σ X0) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) ∨ (k (σ X0) (k X1 (σ X2))) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ X0) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (σ X2) (k X0 (σ X1))
       have i₂ := eq99 X0 X1 X2
       grind)
    | exact superpose eq99 eq13
    | (have j0 := eq13 (σ X0) (k X1 (σ X2))
       have j1 := eq99 X1 X2 X0
       grind)
    | (have r₁ := eq13 (σ X2) (k X0 (σ X1))
       have r₂ := eq99 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k X0 (σ X1)) (σ X2)
       have r₂ := eq99 X0 X1 X2
       grind)
    | exact resolve eq13 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq1046 : ∀ X0 X1 X2 : G, (M.op (σ X0) (k X1 (σ X2))) ≠ (M.op (σ X0) (k X1 (σ X2))) ∨ (σ X0) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) ∨ (k (σ X0) (k X1 (σ X2))) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1027 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027
  have eq1047 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) ∨ (k (σ X0) (k X1 (σ X2))) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1046 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046
  have eq1054 : ∀ X0 X1 X2 : G, (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ X0) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1047 X0 X1 X2
       have i₂ := eq22 X1 X2 X0
       grind)
    | exact superpose eq22 eq1047
    | (have j0 := eq1047 X0 X1 X2
       grind)
    | exact resolve eq1047 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1047
  have eq1055 : ∀ X0 X1 X2 : G, (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ X0) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1054 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054
  have eq2189 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op X1 (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 (M.op X1 (M.op X1 (σ X0)))
       have i₂ := eq476 (σ X0) X1
       grind)
    | exact superpose eq476 eq32
    | exact resolve eq32 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq2193 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (M.op X1 (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op X1 (M.op X1 (τ X0)))
       have i₂ := eq476 (τ X0) X1
       grind)
    | exact superpose eq476 eq18
    | exact resolve eq18 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2196 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 (M.op X1 (τ X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2193 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2193
    | exact resolve eq2193 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2193
  have eq2200 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (M.op X1 (σ X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2189 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2189
    | exact resolve eq2189 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2189
  have eq5671 : ∀ X0 X1 X2 : G, (σ (k X0 X2)) = (M.op (k (σ X0) (M.op X1 (M.op X1 (σ X0)))) (σ X2)) ∨ (M.op (σ X2) (σ X2)) = (k (σ X0) (M.op X1 (M.op X1 (σ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq978 X0 (M.op X1 (M.op X1 (σ X0))) X2
       have i₂ := eq2200 X0 X1
       grind)
    | exact superpose eq2200 eq978
    | (have j0 := eq978 X0 (M.op X1 (M.op X1 (σ X0))) X2
       grind)
    | exact resolve eq978 eq2200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978
  have eq5833 : ∀ X0 X1 X2 : G, (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (M.op (σ X2) (σ X2)) = (k (σ X0) (M.op X1 (M.op X1 (σ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5671 X0 X1 X2
       have i₂ := eq476 (σ X0) X1
       grind)
    | exact superpose eq476 eq5671
    | (have j0 := eq5671 X0 X1 X2
       grind)
    | exact resolve eq5671 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5671
  have eq5885 : ∀ X0 X2 : G, (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (M.op (σ X2) (σ X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq5833 X0 x X2
       have i₂ := eq476 (σ X0) x
       grind)
    | exact superpose eq476 eq5833
    | (have j0 := eq5833 X0 x X2
       grind)
    | exact resolve eq5833 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5833
  have eq6767 : ∀ X0 X1 X2 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) (k X0 (σ (M.op X2 (M.op X2 (τ X0)))))) ∨ (σ X1) = (M.op (k X0 (σ (M.op X2 (M.op X2 (τ X0))))) (k X0 (σ (M.op X2 (M.op X2 (τ X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1055 X1 X0 (M.op X2 (M.op X2 (τ X0)))
       have i₂ := eq476 (τ X0) X2
       grind)
    | exact superpose eq476 eq1055
    | (have j0 := eq1055 X1 X0 (M.op X2 (M.op X2 (τ X0)))
       grind)
    | exact resolve eq1055 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476 eq1055
  have eq6914 : ∀ X0 X1 X2 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (k X0 (σ (M.op X2 (M.op X2 (τ X0))))) (k X0 (σ (M.op X2 (M.op X2 (τ X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6767 X0 X1 X2
       have i₂ := eq2196 X0 X2
       grind)
    | exact superpose eq2196 eq6767
    | (have j0 := eq6767 X0 X1 X2
       grind)
    | exact resolve eq6767 eq2196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6767
  have eq6964 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (k X0 (σ (M.op X2 (M.op X2 (τ X0))))) (k X0 (σ (M.op X2 (M.op X2 (τ X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6914 X0 X1 X2
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq6914
    | (have j0 := eq6914 X0 X1 X2
       grind)
    | exact resolve eq6914 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq6914
  have eq7001 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6964 X0 X1 X1
       have i₂ := eq2196 X0 X1
       grind)
    | exact superpose eq2196 eq6964
    | (have j0 := eq6964 X0 X1 x
       grind)
    | exact resolve eq6964 eq2196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2196 eq6964
  have eq7058 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7001 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7001
    | exact resolve eq7001 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7001
  have eq7563 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq179 x
       have i₂ := eq7058 x x
       grind)
    | exact superpose eq7058 eq179
    | (have j1 := eq7058 X0 X0
       grind)
    | exact resolve eq179 eq7058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq7663 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7563 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7563
  have eq8879 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq242 (τ X0)
       have i₂ := eq7663 X0
       grind)
    | exact superpose eq7663 eq242
    | (have j1 := eq7663 X0
       grind)
    | exact resolve eq242 eq7663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7663
  have eq107379 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5885 x y
       grind)
    | exact superpose eq5885 eq16
    | (have j1 := eq5885 x y
       grind)
    | exact resolve eq16 eq5885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5885
  have eq111755 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq107379
       have i₂ := eq7058 x y
       grind)
    | exact superpose eq7058 eq107379
    | (have j1 := eq7058 (σ x) (σ y)
       grind)
    | exact resolve eq107379 eq7058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111762 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq111755
  have eq111768 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  have eq111777 : x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq242 y
       have i₂ := eq111762
       grind)
    | exact superpose eq111762 eq242
    | exact resolve eq242 eq111762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111762
  have eq113623 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq107379
       have i₂ := eq111768
       grind)
    | exact superpose eq111768 eq107379
    | exact resolve eq107379 eq111768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107379 eq111768
  have eq113677 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq113623
  have eq122566 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq113677
       have i₂ := eq111777
       grind)
    | exact superpose eq111777 eq113677
    | exact resolve eq113677 eq111777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111777 eq113677
  have eq122567 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq122566
  have eq122568 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq122567
  have eq122973 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq68 X0 (σ y)
       have i₂ := eq122568
       grind)
    | exact superpose eq122568 eq68
    | exact resolve eq68 eq122568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq122979 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq242 (σ y)
       have i₂ := eq122568
       grind)
    | exact superpose eq122568 eq242
    | exact resolve eq242 eq122568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq123017 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8879 (σ y)
       have i₂ := eq122568
       grind)
    | exact superpose eq122568 eq8879
    | exact resolve eq8879 eq122568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8879 eq122568
  have eq123108 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq123017
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq123017
    | exact resolve eq123017 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123017
  have eq123155 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq123108
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq123108
    | exact resolve eq123108 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123108
  have eq125058 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq122979
       grind)
    | exact superpose eq122979 eq16
    | exact resolve eq16 eq122979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122979
  have eq127841 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq125058
       have i₂ := eq123155
       grind)
    | exact superpose eq123155 eq125058
    | exact resolve eq125058 eq123155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123155
  have eq127879 : (σ x) = (σ y) := by grind
  clear eq127841
  have eq127890 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq127879
       grind)
    | exact superpose eq127879 eq10
    | exact resolve eq10 eq127879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128078 : ∀ X0 : G, y = (k y (τ (M.op X0 (M.op X0 (σ x))))) := by
    intro X0
    first
    | (have i₁ := eq2200 y X0
       have i₂ := eq127879
       grind)
    | exact superpose eq127879 eq2200
    | exact resolve eq2200 eq127879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2200 eq127879
  have eq128107 : y = (k y (τ (σ y))) := by
    first
    | (have i₁ := eq128078 x
       have i₂ := eq122973 x
       grind)
    | exact superpose eq122973 eq128078
    | exact resolve eq128078 eq122973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122973 eq128078
  have eq128130 : x = y := by
    first
    | (have i₁ := eq127890
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq127890
    | exact resolve eq127890 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127890
  have eq128132 : y = (k y y) := by
    first
    | (have i₁ := eq128107
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq128107
    | exact resolve eq128107 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128107
  have eq128151 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq125058
       have i₂ := eq128130
       grind)
    | exact superpose eq128130 eq125058
    | exact resolve eq125058 eq128130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125058
  have eq128154 : x = (k x x) := by
    first
    | (have i₁ := eq128132
       have i₂ := eq128130
       grind)
    | exact superpose eq128130 eq128132
    | exact resolve eq128132 eq128130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128130 eq128132
  have eq128566 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq7058 x x
       have i₂ := eq128154
       grind)
    | exact superpose eq128154 eq7058
    | (have j0 := eq7058 x x
       grind)
    | exact resolve eq7058 eq128154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7058 eq128154
  have eq128569 : x = (M.op x x) := by grind
  clear eq128566
  have eq129517 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq128151
       have i₂ := eq128569
       grind)
    | exact superpose eq128569 eq128151
    | exact resolve eq128151 eq128569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128151 eq128569
  have eq129518 : False := by grind
  exact eq129518

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pyy_pxy_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq30 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq34 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq114 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq34 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq117 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq114 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq114 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq114 X0 X1
       have r₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact resolve eq114 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq726 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  clear eq117
  have eq735 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq726 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq1438 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq735 (σ X0) (σ X1)
       grind)
    | exact superpose eq735 eq15
    | exact resolve eq15 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1451 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1438 X0 X1
       have i₂ := eq735 X0 X1
       grind)
    | exact superpose eq735 eq1438
    | exact resolve eq1438 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735 eq1438
  have eq1463 : False := by grind
  exact eq1463

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyx_pxy_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
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
  clear eq25
  have eq51 : y = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op y y)) := by
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq23 eq37
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq85
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq85
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq90
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq90
    | exact resolve eq90 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq96
    | exact resolve eq96 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq293 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq296 : (M.op y y) = (M.op x (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (k (M.op X0 (M.op X1 X1)) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq305 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq303 X0 X1
       have i₂ := eq53 (M.op X1 X1) X0
       grind)
    | exact superpose eq53 eq303
    | exact resolve eq303 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq309 : (M.op y y) = (M.op x (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq296
       have i₂ := eq53 sF0 sF0
       grind)
    | exact superpose eq53 eq296
    | exact resolve eq296 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq310 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq294 X0 X1
       have i₂ := eq53 (M.op X1 X1) X0
       grind)
    | exact superpose eq53 eq294
    | exact resolve eq294 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq311 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq293 X0 X1
       have i₂ := eq53 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq53 eq293
    | exact resolve eq293 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq312 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq305 X0 X1
       have i₂ := eq53 X1 X1
       grind)
    | exact superpose eq53 eq305
    | exact resolve eq305 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq315 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq310 X0 X1
       have i₂ := eq53 X1 X1
       grind)
    | exact superpose eq53 eq310
    | exact resolve eq310 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq316 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq311 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq311
    | exact resolve eq311 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq319 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq301 X2 (M.op X0 X1)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq301
    | exact resolve eq301 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq636 : (M.op (M.op y y) (M.op y y)) = (M.op x (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
    first
    | exact superpose eq309 eq53
    | exact resolve eq53 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq641 : (M.op (M.op y y) (M.op y y)) = (M.op x (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq636
       have i₂ := eq53 (M.op sF0 sF0) sF0
       grind)
    | exact superpose eq53 eq636
    | exact resolve eq636 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq643 : (M.op x (M.op x y)) = (M.op (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq641
       have i₂ := eq14 sF0 sF0
       grind)
    | exact superpose eq14 eq641
    | exact resolve eq641 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq644 : (M.op x (M.op x y)) = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq643
       have i₂ := eq53 y y
       grind)
    | exact superpose eq53 eq643
    | exact resolve eq643 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq2619 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq312 X1 (M.op (M.op X1 X0) (M.op X1 X0))
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq312
    | exact resolve eq312 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2647 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq312 X1 (M.op X0 X0)
       have i₂ := eq301 (M.op X0 X0) X0
       grind)
    | exact superpose eq301 eq312
    | exact resolve eq312 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2694 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2619 X0 X1
       have i₂ := eq301 (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 X0)
       grind)
    | exact superpose eq301 eq2619
    | exact resolve eq2619 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2619
  have eq2826 : (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) = (M.op x (M.op y (M.op x (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))))) := by
    first
    | exact superpose eq51 eq316
    | exact resolve eq316 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq2857 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) X1
       have i₂ := eq316 X0 X1
       grind)
    | exact superpose eq316 eq53
    | exact resolve eq53 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2863 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2857 X0 X1
       have i₂ := eq53 (M.op X1 (M.op X0 X0)) (M.op X1 X0)
       grind)
    | exact superpose eq53 eq2857
    | exact resolve eq2857 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2857
  have eq2889 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op x (M.op y (M.op x (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))))) := by
    first
    | (have i₁ := eq2826
       have i₂ := eq53 sF0 sF0
       grind)
    | exact superpose eq53 eq2826
    | exact resolve eq2826 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2826
  have eq2904 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2863 X0 X1
       have i₂ := eq53 (M.op X0 X0) X1
       grind)
    | exact superpose eq53 eq2863
    | exact resolve eq2863 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2863
  have eq2924 : (M.op x (M.op y (M.op y y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq309 eq2889
    | exact resolve eq2889 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309 eq2889
  have eq2938 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2904 X0 X1
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq2904
    | exact resolve eq2904 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2904
  have eq2949 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq2924
       have i₂ := eq644
       grind)
    | exact superpose eq644 eq2924
    | exact resolve eq2924 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2924
  have eq2960 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2938 X0 X1
       have i₂ := eq312 X1 X0
       grind)
    | exact superpose eq312 eq2938
    | exact resolve eq2938 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312 eq2938
  have eq3015 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq2960 y X0
       have i₂ := eq644
       grind)
    | exact superpose eq644 eq2960
    | exact resolve eq2960 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq4238 : ∀ X0 X1 : G, (k (M.op X0 (M.op X1 X1)) (M.op X0 X1)) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq304 X0 X1
       have i₂ := eq315 X0 X1
       grind)
    | exact superpose eq315 eq304
    | exact resolve eq304 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304 eq315
  have eq4307 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) = (k X0 (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4238 X1 (M.op X1 X0)
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq4238
    | exact resolve eq4238 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4238
  have eq4439 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))) = (k X0 (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4307 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq4307
    | exact resolve eq4307 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4307
  have eq4499 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4439 X0 X1
       have i₂ := eq316 X0 X1
       grind)
    | exact superpose eq316 eq4439
    | exact resolve eq4439 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316 eq4439
  have eq13446 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq319 X1 X1 X2
       have i₂ := eq2960 X1 X0
       grind)
    | (have i₁ := eq319 X0 X0 X2
       have i₂ := eq2960 X0 X0
       grind)
    | exact superpose eq2960 eq319
    | exact resolve eq319 eq2960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319 eq2960
  have eq19838 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19839 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq19838
    | exact resolve eq19838 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19838
  have eq19850 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq19839
       have r₂ := eq28
       grind)
    | exact resolve eq19839 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19839
  have eq19869 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op X0 (M.op (σ y) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq19850 eq13446
    | exact resolve eq13446 eq19850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19850
  have eq19872 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq19869 x
       have i₂ := eq301 x sF3
       grind)
    | exact superpose eq301 eq19869
    | exact resolve eq19869 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19869
  have eq19873 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq19872
  have eq19881 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq19873
  have eq19938 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq19881
    | exact resolve eq19881 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19881
  have eq20955 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq19938 eq97
    | exact resolve eq97 eq19938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq19938
  have eq20966 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq20955
  have eq20968 : y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq20966
       have r₂ := eq28
       grind)
    | exact resolve eq20966 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20966
  have eq20987 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op X0 (M.op y y))) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq13446 y x X0
       have i₂ := eq20968
       grind)
    | exact superpose eq20968 eq13446
    | exact resolve eq13446 eq20968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20968
  have eq20990 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq20987 x
       have i₂ := eq301 x y
       grind)
    | exact superpose eq301 eq20987
    | exact resolve eq20987 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20987
  have eq20991 : y = (M.op x x) := by grind
  clear eq20990
  have eq21016 : x = (M.op x (M.op y y)) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq20991
       grind)
    | exact superpose eq20991 eq14
    | exact resolve eq14 eq20991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21017 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq53 x x
       have i₂ := eq20991
       grind)
    | exact superpose eq20991 eq53
    | exact resolve eq53 eq20991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq21021 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq2694 x x
       have i₂ := eq20991
       grind)
    | exact superpose eq20991 eq2694
    | exact resolve eq2694 eq20991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2694
  have eq21042 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq21021
       have i₂ := eq3015 x
       grind)
    | (have i₁ := eq21021
       have i₂ := eq3015 x
       grind)
    | exact superpose eq3015 eq21021
    | exact resolve eq21021 eq3015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3015 eq21021
  have eq21045 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq21017
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq21017
    | exact resolve eq21017 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq21017
  have eq21046 : x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq21016
       have i₂ := eq54
       grind)
    | exact superpose eq54 eq21016
    | exact resolve eq21016 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq21016
  have eq21892 : (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) = (M.op (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) (M.op x (M.op x (M.op x y)))) := by
    first
    | exact superpose eq2949 eq2647
    | exact resolve eq2647 eq2949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2647 eq2949
  have eq21987 : (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) = (M.op (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) (M.op x x)) := by
    first
    | exact superpose eq21042 eq21892
    | exact resolve eq21892 eq21042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21042 eq21892
  have eq22078 : (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) = (M.op (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) y) := by
    first
    | (have i₁ := eq21987
       have i₂ := eq20991
       grind)
    | exact superpose eq20991 eq21987
    | exact resolve eq21987 eq20991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20991 eq21987
  have eq22128 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq22078
       have i₂ := eq14 sF0 sF0
       grind)
    | exact superpose eq14 eq22078
    | exact resolve eq22078 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22078
  have eq22182 : (M.op y y) = (k y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq22128 eq4499
    | exact resolve eq4499 eq22128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4499 eq22128
  have eq22186 : (M.op y y) = (k y x) := by
    first
    | exact superpose eq21046 eq22182
    | exact resolve eq22182 eq21046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21046 eq22182
  have eq22204 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq22186
       have i₂ := eq21045
       grind)
    | exact superpose eq21045 eq22186
    | exact resolve eq22186 eq21045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21045 eq22186
  have eq22227 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq85
       have i₂ := eq22204
       grind)
    | exact superpose eq22204 eq85
    | exact resolve eq85 eq22204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq22204
  have eq22251 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq21 eq22227
    | exact resolve eq22227 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq22227
  have eq22289 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq22251 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq22251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22290 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq22289
    | exact resolve eq22289 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22289
  have eq22301 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq22290
       have r₂ := eq28
       grind)
    | exact resolve eq22290 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22290
  have eq32952 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op X0 (M.op (σ y) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq22301 eq13446
    | exact resolve eq13446 eq22301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13446 eq22301
  have eq32955 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq32952 x
       have i₂ := eq301 x sF3
       grind)
    | exact superpose eq301 eq32952
    | exact resolve eq32952 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301 eq32952
  have eq32956 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq32955
  have eq32967 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq32956
  have eq33035 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22251 eq32967
    | exact resolve eq32967 eq22251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22251 eq32967
  have eq33039 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq33035
    | exact resolve eq33035 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq33035
  have eq33040 : False := by grind
  exact eq33040

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pxx_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
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
  clear eq36
  have eq51 : y = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq84 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq79
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq79
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq79 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq90
    | exact resolve eq90 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq91
    | exact resolve eq91 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq98 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq98 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq98
    | (have j0 := eq98 (σ X0)
       grind)
    | exact resolve eq98 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq98 x
       grind)
    | exact superpose eq98 eq44
    | (have j1 := eq98 x
       grind)
    | exact resolve eq44 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq316 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq327 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (k (M.op X0 (M.op X1 X1)) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq334 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq316 X0 X1
       have i₂ := eq53 (M.op X1 X1) X0
       grind)
    | exact superpose eq53 eq316
    | exact resolve eq316 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq339 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq334 X0 X1
       have i₂ := eq53 X1 X1
       grind)
    | exact superpose eq53 eq334
    | exact resolve eq334 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq342 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq323 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq323 (M.op X0 X0) X0
       grind)
    | exact superpose eq323 eq323
    | exact resolve eq323 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3813 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq3831 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq282 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq3834 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3813 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq3813
    | (have j0 := eq3813 X0
       grind)
    | exact resolve eq3813 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3813
  have eq4506 : ∀ X0 X1 : G, (k (M.op X0 (M.op X1 X1)) (M.op X0 X1)) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq327 X0 X1
       have i₂ := eq339 X0 X1
       grind)
    | exact superpose eq339 eq327
    | exact resolve eq327 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327 eq339
  have eq4577 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4506 (M.op x x) (M.op x x)
       have i₂ := eq323 (M.op x x) x
       grind)
    | exact superpose eq323 eq4506
    | exact resolve eq4506 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323 eq4506
  have eq4710 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4577 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq4577
    | exact resolve eq4577 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq4577
  have eq4771 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4710 X0
       have i₂ := eq342 X0
       grind)
    | exact superpose eq342 eq4710
    | exact resolve eq4710 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq4710
  have eq22325 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq92 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22326 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq22325
    | exact resolve eq22325 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22325
  have eq22337 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq22326
       have r₂ := eq28
       grind)
    | exact resolve eq22326 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22326
  have eq22339 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq22337
    | exact resolve eq22337 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22337
  have eq22364 : (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22339 eq14
    | exact resolve eq14 eq22339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22339
  have eq22387 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq52 eq22364
    | exact resolve eq22364 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq22364
  have eq22394 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq22387
  have eq22463 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq22394
    | exact resolve eq22394 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22394
  have eq23488 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22463 eq92
    | exact resolve eq92 eq22463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq22463
  have eq23496 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq23488
  have eq23498 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq23496
       have r₂ := eq28
       grind)
    | exact resolve eq23496 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23496
  have eq23788 : x = (M.op x (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq23498
       grind)
    | exact superpose eq23498 eq14
    | exact resolve eq14 eq23498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23498
  have eq23811 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq51 eq23788
    | exact resolve eq23788 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq23788
  have eq23816 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq286
       have i₂ := eq23811
       grind)
    | exact superpose eq23811 eq286
    | exact resolve eq286 eq23811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23819 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  have eq23837 : y ≠ y ∨ x = y ∨ y = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq23811
       grind)
    | exact superpose eq23811 eq12
    | exact resolve eq12 eq23811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23811
  have eq23856 : y ≠ y ∨ x = y ∨ y = (k x x) ∨ (σ x) = (σ y) := by grind
  clear eq23837
  have eq23857 : y = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq23856
  have eq23859 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq23816
  have eq23889 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq23819
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq23819
    | exact resolve eq23819 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23819
  have eq23890 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq23859
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq23859
    | exact resolve eq23859 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23859
  have eq24595 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq23889
       grind)
    | exact superpose eq23889 eq79
    | exact resolve eq79 eq23889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23889
  have eq24613 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq24595
    | exact resolve eq24595 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24595
  have eq115538 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3834 x
       have i₂ := eq23857
       grind)
    | exact superpose eq23857 eq3834
    | (have j0 := eq3834 x
       grind)
    | exact resolve eq3834 eq23857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3834 eq23857
  have eq115602 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq115538
       have i₂ := eq79
       grind)
    | exact superpose eq79 eq115538
    | exact resolve eq115538 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq115538
  have eq115633 : (k (σ y) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq115602
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq115602
    | exact resolve eq115602 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115602
  have eq115654 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq115633
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq115633
    | exact resolve eq115633 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115633
  have eq115666 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq115654
    | exact resolve eq115654 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115654
  have eq115674 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq115666
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq115666
    | exact resolve eq115666 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115666
  have eq217157 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq115674 eq24613
    | exact resolve eq24613 eq115674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24613 eq115674
  have eq217163 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq217157
  have eq217171 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq217163
       have r₂ := eq28
       grind)
    | exact resolve eq217163 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217163
  have eq217181 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  have eq217270 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq217181 eq23890
    | exact resolve eq23890 eq217181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23890 eq217181
  have eq217295 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq217270
  have eq217310 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq217295 eq217171
    | exact resolve eq217171 eq217295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217171 eq217295
  have eq217371 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq217310
  have eq217885 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq217371 eq30
    | exact resolve eq30 eq217371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq217371
  have eq218053 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq217885
    | exact resolve eq217885 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq217885
  have eq218054 : x = y := by grind
  clear eq218053
  have eq218055 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq218054
       grind)
    | exact superpose eq218054 eq19
    | exact resolve eq19 eq218054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq218056 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq218054
       grind)
    | exact superpose eq218054 eq25
    | exact resolve eq25 eq218054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq218054
  have eq218404 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq218056
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq218056
    | exact resolve eq218056 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218056
  have eq218405 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq218404 eq27
    | exact resolve eq27 eq218404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq218404
  have eq219619 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq286
       have i₂ := eq218055
       grind)
    | exact superpose eq218055 eq286
    | exact resolve eq286 eq218055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq219730 : (M.op x y) = (k x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq4771 x
       have i₂ := eq218055
       grind)
    | exact superpose eq218055 eq4771
    | exact resolve eq4771 eq218055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4771
  have eq219771 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq219619
    | exact resolve eq219619 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219619
  have eq219790 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq263294 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq219771 eq98
    | (have j0 := eq98 (σ x)
       grind)
    | exact resolve eq98 eq219771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq263309 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq218405 eq263294
    | exact resolve eq263294 eq218405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263294
  have eq263322 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq263309
       have r₂ := eq28
       grind)
    | exact resolve eq263309 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263309
  have eq263328 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq218405 eq263322
    | exact resolve eq263322 eq218405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263322
  have eq263361 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq263328 eq219790
    | exact resolve eq219790 eq263328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219790 eq263328
  have eq263375 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq218405 eq263361
    | exact resolve eq263361 eq218405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263361
  have eq268835 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq263375 eq219771
    | exact resolve eq219771 eq263375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219771 eq263375
  have eq268851 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq268835
  have eq268856 : x = (M.op x y) := by
    first
    | (have r₁ := eq268851
       have r₂ := eq28
       grind)
    | exact resolve eq268851 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268851
  have eq268865 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq268856 eq21
    | exact resolve eq21 eq268856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq269541 : x = (k x (M.op x x)) := by
    first
    | exact superpose eq268856 eq219730
    | exact resolve eq219730 eq268856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219730
  have eq269547 : x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq269541
       have i₂ := eq218055
       grind)
    | exact superpose eq218055 eq269541
    | exact resolve eq269541 eq218055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218055 eq269541
  have eq269717 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq268865
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq268865
    | exact resolve eq268865 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268865
  have eq269720 : x = (k x x) := by
    first
    | exact superpose eq268856 eq269547
    | exact resolve eq269547 eq268856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268856 eq269547
  have eq272188 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3831 x
       have i₂ := eq269720
       grind)
    | exact superpose eq269720 eq3831
    | (have j0 := eq3831 x
       grind)
    | exact resolve eq3831 eq269720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3831 eq269720
  have eq272194 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq272188
  have eq272206 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq272194
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq272194
    | exact resolve eq272194 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq272194
  have eq272230 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq218405 eq272206
    | exact resolve eq272206 eq218405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218405 eq272206
  have eq272252 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq269717 eq272230
    | exact resolve eq272230 eq269717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269717 eq272230
  have eq272272 : False := by grind
  exact eq272272
