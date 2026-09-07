import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3318`: `x ◇ y = x ◇ (y ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pxy_y_pxy_Equation3318 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3318 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3318.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
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
  have eq25 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq23
  have eq43 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    grind
  have eq46 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq43 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq43
    | (have j0 := eq43 X0
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq66 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq14 (M.op X0 (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq66 (M.op X0 X1) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq66 (k X0 X1) (M.op X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq66 (M.op X0 (k X1 X1)) X1
       have r₂ := eq12 X0 (k X1 X1)
       grind)
    | exact resolve eq66 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq381 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 X0
       have i₂ := eq14 X0 (σ X0)
       grind)
    | (have i₁ := eq63 X0 X1
       have i₂ := eq14 (M.op (σ X0) (σ X1)) X1
       grind)
    | exact superpose eq14 eq63
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq63 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq409 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq10
    | (have j1 := eq63 X1 X0
       grind)
    | exact resolve eq10 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq436 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq63 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq438 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq436 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq446 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq381 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq466 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq446 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq446 (M.op X0 (σ (k X1 X1))) X1
       have r₂ := eq12 X0 (σ (k X1 X1))
       grind)
    | (have r₁ := eq446 (M.op X0 (σ X1)) X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq446 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq446 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq528 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq438 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq438
    | (have j0 := eq438 (τ X0)
       grind)
    | exact resolve eq438 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq531 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq528 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq528
    | (have j0 := eq528 X0
       grind)
    | exact resolve eq528 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq534 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq531 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq531
    | (have j0 := eq531 X0
       grind)
    | exact resolve eq531 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq543 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq534 (τ X0)
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq534
    | (have j0 := eq534 (τ X0)
       grind)
    | exact resolve eq534 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq534
  have eq1627 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq466 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq466
    | (have j0 := eq466 X1 (τ X0)
       grind)
    | exact resolve eq466 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq1729 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1627 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq1627
    | (have j0 := eq1627 X0 X1
       grind)
    | exact resolve eq1627 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1627
  have eq1738 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1729 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1729
    | (have j0 := eq1729 X0 X1
       grind)
    | exact resolve eq1729 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1729
  have eq1744 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1738 X0 X1
       have j1 := eq72 X1 X0
       grind)
    | (have r₁ := eq1738 X0 X1
       have r₂ := eq72 (k X0 X0) X1
       grind)
    | (have r₁ := eq1738 X0 X0
       have r₂ := eq72 X0 (k X0 X0)
       grind)
    | (have r₁ := eq1738 X0 X1
       have r₂ := eq72 (M.op X1 X0) (k X1 X0)
       grind)
    | exact resolve eq1738 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq1738
  have eq1973 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (τ X1) = (M.op X0 (τ X1)) ∨ (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (τ X1) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0
       have i₂ := eq14 X0 (τ X0)
       grind)
    | (have i₁ := eq46 X0
       have i₂ := eq14 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact superpose eq14 eq46
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq46 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq2015 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (τ X1) = (M.op X0 (τ X1)) ∨ (k X0 (τ X1)) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1973 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1973
  have eq2035 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2015 X0 X1
       have j1 := eq12 X0 (τ X1)
       grind)
    | (have r₁ := eq2015 X0 X1
       have r₂ := eq12 X0 (τ X1)
       grind)
    | exact resolve eq2015 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2015
  have eq5586 : ∀ X0 : G, (τ (σ X0)) ≠ (τ (σ X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq543 (σ X0)
       have i₂ := eq2035 X0 (σ X0)
       grind)
    | exact superpose eq2035 eq543
    | (have j0 := eq543 (σ X0)
       have j1 := eq2035 X0 (σ X0)
       grind)
    | exact resolve eq543 eq2035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543 eq2035
  have eq5596 : ∀ X0 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq5586 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5586
  have eq5604 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq5596 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5596
    | (have j0 := eq5596 X0
       grind)
    | exact resolve eq5596 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5596
  have eq5616 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5604 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5604
    | (have j0 := eq5604 X0
       grind)
    | exact resolve eq5604 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5604
  have eq5619 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq5616 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq5616 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq5616 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5616
  have eq5721 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1744 X0 X1
       have i₂ := eq5619 X0
       grind)
    | exact superpose eq5619 eq1744
    | (have j0 := eq1744 X0 X1
       grind)
    | exact resolve eq1744 eq5619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1744
  have eq5737 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq5619 (σ X0)
       grind)
    | exact superpose eq5619 eq15
    | exact resolve eq15 eq5619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5759 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5737 X0
       have i₂ := eq5619 X0
       grind)
    | exact superpose eq5619 eq5737
    | exact resolve eq5737 eq5619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5619 eq5737
  have eq5853 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq409 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq409
    | exact resolve eq409 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq5954 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5853 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq5853
    | (have j0 := eq5853 X0 X1
       grind)
    | exact resolve eq5853 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq5853
  have eq6034 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5954 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq5954 X0 (M.op X0 (τ (M.op X0 X0)))
       have r₂ := eq12 X0 (τ (M.op X0 X0))
       grind)
    | (have r₁ := eq5954 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq5954 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5954
  have eq6463 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq25 (σ X0)
       have i₂ := eq5759 X0
       grind)
    | exact superpose eq5759 eq25
    | exact resolve eq25 eq5759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6511 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq6463 X0
       have i₂ := eq5759 (M.op X0 X0)
       grind)
    | exact superpose eq5759 eq6463
    | exact resolve eq6463 eq5759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6463
  have eq6538 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq6511 X0
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq6511
    | exact resolve eq6511 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq6511
  have eq7557 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (M.op (σ X1) (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq6034 (σ X1) X0
       grind)
    | exact superpose eq6034 eq15
    | (have j1 := eq6034 (σ X1) X0
       grind)
    | exact resolve eq15 eq6034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6034
  have eq7622 : ∀ X0 X1 : G, (τ (σ (M.op X1 X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7557 X0 X1
       have i₂ := eq5759 X1
       grind)
    | exact superpose eq5759 eq7557
    | (have j0 := eq7557 X0 X1
       grind)
    | exact resolve eq7557 eq5759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5759 eq7557
  have eq7653 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7622 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq7622
    | (have j0 := eq7622 X0 X1
       grind)
    | exact resolve eq7622 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7622
  have eq21976 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7653 x y
       grind)
    | exact superpose eq7653 eq16
    | (have j1 := eq7653 x y
       grind)
    | exact resolve eq16 eq7653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7653
  have eq22534 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq21976
       have i₂ := eq5721 y x
       grind)
    | exact superpose eq5721 eq21976
    | (have j1 := eq5721 y x
       grind)
    | exact resolve eq21976 eq5721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5721 eq21976
  have eq22543 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by grind
  clear eq22534
  have eq22544 : x = (M.op y y) := by grind
  clear eq22543
  have eq22823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6538 y
       have i₂ := eq22544
       grind)
    | exact superpose eq22544 eq6538
    | exact resolve eq6538 eq22544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6538 eq22544
  have eq22858 : False := by grind
  exact eq22858

/-- `Equation3321`: `x ◇ y = x ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_pyx_x_pyx_Equation3321 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3321 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3321.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq25 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X0 X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq23
  have eq62 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X2 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X2 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq62 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq75 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq73 (k X0 X1) (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq73 (M.op X1 X0) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq73 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq73 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq85 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq75 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq97 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq85 (σ X0)
       grind)
    | exact superpose eq85 eq15
    | exact resolve eq15 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq85 (τ X0)
       grind)
    | exact superpose eq85 eq19
    | exact resolve eq19 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq102 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq101 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq101
    | exact resolve eq101 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq106 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq97 X0
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq97
    | exact resolve eq97 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq108 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq102
    | exact resolve eq102 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq157 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq85 (τ X0)
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq85
    | exact resolve eq85 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq160 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq157 X0
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq157
    | exact resolve eq157 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq157
  have eq197 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq14
    | (have j0 := eq14 (σ X0) X1
       grind)
    | exact resolve eq14 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq197 X0 X1
       have j1 := eq199 X0 X1
       grind)
    | (have r₁ := eq197 X0 X1
       have r₂ := eq199 X0 X1
       grind)
    | (have r₁ := eq197 X0 (σ (M.op (M.op X0 X0) (M.op X0 X0)))
       have r₂ := eq199 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq197 X0 (σ X0)
       have r₂ := eq199 X0 X1
       grind)
    | exact resolve eq197 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq199
  have eq235 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq106 (M.op (τ X0) (τ X0))
       have i₂ := eq108 X0
       grind)
    | exact superpose eq108 eq106
    | exact resolve eq106 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq245 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq235 X0
       have i₂ := eq25 (τ X0) (τ X0) (τ X0)
       grind)
    | exact superpose eq25 eq235
    | exact resolve eq235 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq248 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq245 X0
       have i₂ := eq160 X0
       grind)
    | exact superpose eq160 eq245
    | exact resolve eq245 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq245
  have eq250 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq248 X0
       have i₂ := eq25 X0 X0 X0
       grind)
    | exact superpose eq25 eq248
    | exact resolve eq248 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq248
  have eq376 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq377 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq376 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq1059 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (τ (M.op (σ X0) (σ X0))) X0)) := by
    intro X0
    first
    | (have i₁ := eq250 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq250
    | exact resolve eq250 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq1086 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (τ (σ (M.op X0 X0))) X0)) := by
    intro X0
    first
    | (have i₁ := eq1059 X0
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq1059
    | exact resolve eq1059 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq1059
  have eq1104 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq1086 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1086
    | exact resolve eq1086 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086
  have eq2899 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq201 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq201 X0 (σ X0)
       grind)
    | exact superpose eq201 eq10
    | (have j1 := eq201 X1 X0
       grind)
    | exact resolve eq10 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq6885 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq2899 (σ X0) X1
       grind)
    | exact superpose eq2899 eq15
    | (have j1 := eq2899 (σ X0) X1
       grind)
    | exact resolve eq15 eq2899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2899
  have eq6921 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6885 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6885
    | (have j0 := eq6885 X0 X1
       grind)
    | exact resolve eq6885 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6885
  have eq10023 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6921 x y
       grind)
    | exact superpose eq6921 eq16
    | (have j1 := eq6921 x y
       grind)
    | exact resolve eq16 eq6921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6921
  have eq10545 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10023
       have i₂ := eq377 y x
       grind)
    | exact superpose eq377 eq10023
    | (have j1 := eq377 y x
       grind)
    | exact resolve eq10023 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377 eq10023
  have eq10551 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by grind
  clear eq10545
  have eq10552 : x = (M.op y y) := by grind
  clear eq10551
  have eq10872 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1104 y
       have i₂ := eq10552
       grind)
    | exact superpose eq10552 eq1104
    | exact resolve eq1104 eq10552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104 eq10552
  have eq10915 : False := by grind
  exact eq10915

/-- `Equation3321`: `x ◇ y = x ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_pyx_x_pxy_pyx_Equation3321 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3321 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3321.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq21 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X0 X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq34 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq40 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq49 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq92 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X1 X2) (M.op X0 X1)) ∨ (M.op X1 X2) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X2 X0) (M.op X0 X1)
       have i₂ := eq21 X0 X1 X2
       grind)
    | exact superpose eq21 eq13
    | (have j0 := eq13 (M.op X0 X1) (M.op X1 X2)
       grind)
    | exact resolve eq13 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq40 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq40 X0 X1
       grind)
    | exact superpose eq40 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq40 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq40 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq40 X0 X1
       grind)
    | exact resolve eq13 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq381 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq334 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq382 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq381 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq394 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq382 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq382
    | (have j0 := eq382 X0 X1
       grind)
    | exact resolve eq382 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq395 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq394 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq1563 : ∀ X0 X1 : G, (M.op X0 X0) = (σ X1) ∨ (σ (k (τ X0) X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq395 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq395
    | exact resolve eq395 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq1679 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1563 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq1563
    | (have j0 := eq1563 X0 X1
       grind)
    | exact resolve eq1563 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1563
  have eq2491 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1679 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1679
    | exact resolve eq1679 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2580 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq1679 X0 X1
       grind)
    | exact superpose eq1679 eq10
    | (have j1 := eq1679 X0 X1
       grind)
    | exact resolve eq10 eq1679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1679
  have eq2702 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X1 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq2491 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq2491 (M.op X1 X0) X1
       grind)
    | exact superpose eq2491 eq13
    | (have j1 := eq2491 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq2491 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq2491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2770 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq2491 (τ X0) X1
       grind)
    | exact superpose eq2491 eq19
    | (have j1 := eq2491 (τ X0) X1
       grind)
    | exact resolve eq19 eq2491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2797 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2702 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2702
  have eq11391 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2580 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2580
    | (have j0 := eq2580 X1 (τ X0)
       grind)
    | exact resolve eq2580 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2580
  have eq11796 : ∀ X0 X1 X2 : G, (k (τ X1) (τ X0)) = (τ (k X1 (M.op X2 X2))) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 (M.op X2 X2) X1
       have i₂ := eq11391 X0 X2
       grind)
    | (have i₁ := eq49 X0 X1
       have i₂ := eq11391 X0 X1
       grind)
    | exact superpose eq11391 eq49
    | (have j1 := eq11391 X0 X2
       grind)
    | exact resolve eq49 eq11391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11391
  have eq11807 : ∀ X0 X1 X2 : G, (τ (k X1 X0)) = (τ (k X1 (M.op X2 X2))) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11796 X0 X1 X2
       have i₂ := eq49 X0 X1
       grind)
    | exact superpose eq49 eq11796
    | (have j0 := eq11796 X0 X1 X2
       grind)
    | exact resolve eq11796 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq11796
  have eq18884 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X1 X0) X0) ∨ (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X1 X0)) ∨ (M.op (M.op X1 X0) X0) = (k (M.op X1 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 X1 X0 X1
       have i₂ := eq21 X1 X0 X0
       grind)
    | exact superpose eq21 eq92
    | (have j0 := eq92 X1 X0 X1
       grind)
    | (have r₁ := eq92 X1 X1 X1
       have r₂ := eq21 X1 X1 X1
       grind)
    | exact resolve eq92 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq34266 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2770 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2770
    | exact resolve eq2770 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2770
  have eq34863 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34266 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq34266
    | (have j0 := eq34266 X0 X1
       grind)
    | exact resolve eq34266 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34266
  have eq35942 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X1 X1) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq34863 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq34863 (M.op X1 X0) X1
       grind)
    | exact superpose eq34863 eq13
    | (have j1 := eq34863 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq34863 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq34863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36188 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq35942 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35942
  have eq111368 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k X0 (M.op X2 X2)) ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X0 (M.op X2 X2))
       have i₂ := eq11807 X1 X0 X2
       grind)
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq11807 X0 X1 X2
       grind)
    | exact superpose eq11807 eq11
    | (have j1 := eq11807 X1 X1 X2
       grind)
    | exact resolve eq11 eq11807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11807
  have eq111411 : ∀ X0 X1 X2 : G, (k X0 X1) = (k X0 (M.op X2 X2)) ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq111368 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq111368
    | (have j0 := eq111368 X0 X1 X2
       grind)
    | exact resolve eq111368 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111368
  have eq111804 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 (M.op X0 X0)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq111411 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111411
  have eq111807 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq111804
  have eq111827 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq111807 X1 X1
       have i₂ := eq2491 X0 X1
       grind)
    | (have i₁ := eq111807 X0 X1
       have i₂ := eq2491 (M.op X1 X0) X1
       grind)
    | exact superpose eq2491 eq111807
    | (have j0 := eq111807 X1 X0
       have j1 := eq2491 X0 X1
       grind)
    | (have r₁ := eq111807 X0 X0
       have r₂ := eq2491 X0 X0
       grind)
    | (have r₁ := eq111807 (M.op X1 X1) X1
       have r₂ := eq2491 (M.op X1 (M.op X1 X1)) X1
       grind)
    | exact resolve eq111807 eq2491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111832 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq111807 X1 X1
       have i₂ := eq34863 X0 X1
       grind)
    | (have i₁ := eq111807 X0 X1
       have i₂ := eq34863 (M.op X1 X0) X1
       grind)
    | exact superpose eq34863 eq111807
    | (have j1 := eq34863 X0 X1
       grind)
    | (have r₁ := eq111807 X0 X0
       have r₂ := eq34863 X0 X0
       grind)
    | (have r₁ := eq111807 (M.op X1 X1) X1
       have r₂ := eq34863 (M.op X1 (M.op X1 X1)) X1
       grind)
    | exact resolve eq111807 eq34863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34863
  have eq111850 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (M.op (M.op X0 X1) X1) ∨ (M.op (M.op X0 X1) X1) = (k (M.op X1 X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq111807 (M.op X0 X1) (M.op X2 X0)
       have i₂ := eq21 X0 X1 X2
       grind)
    | exact superpose eq21 eq111807
    | exact resolve eq111807 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111807
  have eq111918 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq111832 X0 X1
       have j1 := eq36188 X0 X1
       grind)
    | (have r₁ := eq111832 (σ (k X1 X0)) (σ (M.op X0 X1))
       have r₂ := eq36188 X0 X1
       grind)
    | (have r₁ := eq111832 (σ (M.op X0 X1)) (σ (k X1 X0))
       have r₂ := eq36188 X0 X1
       grind)
    | (have r₁ := eq111832 (k X1 X1) X0
       have r₂ := eq36188 X0 X1
       grind)
    | exact resolve eq111832 eq36188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36188 eq111832
  have eq111923 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq111827 X0 X1
       have j1 := eq2797 X0 X1
       grind)
    | (have r₁ := eq111827 (M.op X0 X1) (k X1 X0)
       have r₂ := eq2797 X0 X1
       grind)
    | (have r₁ := eq111827 (k X1 X0) (M.op X0 X1)
       have r₂ := eq2797 X0 X1
       grind)
    | (have r₁ := eq111827 (k X1 X1) X0
       have r₂ := eq2797 X0 X1
       grind)
    | exact resolve eq111827 eq2797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2797 eq111827
  have eq112172 : ∀ X0 X1 : G, (τ X0) = (k X1 (τ (σ X1))) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (σ X1)
       have i₂ := eq111923 X0 (σ X1)
       grind)
    | (have i₁ := eq34 X0 X1
       have i₂ := eq111923 (k (σ X0) X1) X1
       grind)
    | exact superpose eq111923 eq34
    | (have j1 := eq111923 X0 (σ X1)
       grind)
    | exact resolve eq34 eq111923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq112420 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq112172 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq112172
    | (have j0 := eq112172 X0 X1
       grind)
    | exact resolve eq112172 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112172
  have eq114713 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq112420 (σ X0) X1
       grind)
    | exact superpose eq112420 eq15
    | (have j1 := eq112420 (σ X0) X1
       grind)
    | exact resolve eq15 eq112420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112420
  have eq114763 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq114713 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq114713
    | (have j0 := eq114713 X0 X1
       grind)
    | exact resolve eq114713 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114713
  have eq116312 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq114763 x y
       grind)
    | exact superpose eq114763 eq16
    | (have j1 := eq114763 x y
       grind)
    | exact resolve eq16 eq114763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114763
  have eq116419 : x = (k y y) := by
    first
    | (have j1 := eq111918 x y
       grind)
    | (have r₁ := eq116312
       have r₂ := eq111918 x y
       grind)
    | exact resolve eq116312 eq111918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111918 eq116312
  have eq116623 : y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2491 y y
       have i₂ := eq116419
       grind)
    | exact superpose eq116419 eq2491
    | (have j0 := eq2491 y y
       grind)
    | exact resolve eq2491 eq116419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116649 : x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq111923 y y
       have i₂ := eq116419
       grind)
    | exact superpose eq116419 eq111923
    | exact resolve eq111923 eq116419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111923 eq116419
  have eq117233 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq116623
  have eq117252 : x = (M.op y y) := by
    first
    | (have r₁ := eq117233
       have r₂ := eq116649
       grind)
    | exact resolve eq117233 eq116649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116649 eq117233
  have eq117320 : ∀ X0 : G, (M.op x y) = (M.op x (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq21 y x y
       have i₂ := eq117252
       grind)
    | exact superpose eq117252 eq21
    | exact resolve eq21 eq117252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117671 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq117320 y
       have i₂ := eq117252
       grind)
    | exact superpose eq117252 eq117320
    | exact resolve eq117320 eq117252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117320
  have eq134598 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq18884 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18884
  have eq134599 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq134598 X0
       have i₂ := eq21 X0 X0 X0
       grind)
    | exact superpose eq21 eq134598
    | (have j0 := eq134598 X0
       grind)
    | exact resolve eq134598 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq134598
  have eq134600 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq134599 X0
       have j1 := eq111850 X0 X0 X0
       grind)
    | (have r₁ := eq134599 X0
       have r₂ := eq111850 X0 X0 X0
       grind)
    | exact resolve eq134599 eq111850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111850 eq134599
  have eq134603 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq134600 X1
       have i₂ := eq2491 X0 X1
       grind)
    | (have i₁ := eq134600 X0
       have i₂ := eq2491 (M.op X0 X0) X1
       grind)
    | exact superpose eq2491 eq134600
    | (have j1 := eq2491 X0 X1
       grind)
    | exact resolve eq134600 eq2491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2491 eq134600
  have eq135696 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq134603 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134603
  have eq135697 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq135696 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135696
  have eq136174 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq135697 (σ X0)
       grind)
    | exact superpose eq135697 eq15
    | exact resolve eq15 eq135697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136242 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq136174 X0
       have i₂ := eq135697 X0
       grind)
    | exact superpose eq135697 eq136174
    | exact resolve eq136174 eq135697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135697 eq136174
  have eq137052 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ X0) (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq136242 X0
       grind)
    | exact superpose eq136242 eq9
    | exact resolve eq9 eq136242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140011 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq137052 y X0
       have i₂ := eq117252
       grind)
    | exact superpose eq117252 eq137052
    | exact resolve eq137052 eq117252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137052
  have eq140268 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ x) (σ y) X0
       have i₂ := eq140011 X0
       grind)
    | exact superpose eq140011 eq9
    | exact resolve eq9 eq140011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140011
  have eq140439 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op y y))) := by
    first
    | (have i₁ := eq140268 (σ y)
       have i₂ := eq136242 y
       grind)
    | exact superpose eq136242 eq140268
    | exact resolve eq140268 eq136242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140268
  have eq140540 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq140439
       have i₂ := eq117252
       grind)
    | exact superpose eq117252 eq140439
    | exact resolve eq140439 eq117252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117252 eq140439
  have eq140551 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq140540
       have i₂ := eq136242 x
       grind)
    | exact superpose eq136242 eq140540
    | exact resolve eq140540 eq136242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136242 eq140540
  have eq140571 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq140551
       grind)
    | exact superpose eq140551 eq16
    | exact resolve eq16 eq140551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140551
  have eq140691 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq140571
       have i₂ := eq117671
       grind)
    | exact superpose eq117671 eq140571
    | exact resolve eq140571 eq117671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117671 eq140571
  have eq140692 : False := by grind
  exact eq140692

/-- `Equation333`: `x ◇ y = y ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation333 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law333 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law333.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X1)
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq36 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq12
    | (have j0 := eq12 (M.op X0 X1) (M.op X0 X1)
       grind)
    | (have r₁ := eq12 (M.op X0 X1) (M.op X0 X1)
       have r₂ := eq17 X0 X1
       grind)
    | exact resolve eq12 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq102 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq36 x y
       grind)
    | exact superpose eq36 eq16
    | (have j1 := eq36 x y
       grind)
    | exact resolve eq16 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq497 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq110 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq110
    | (have j0 := eq110 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact resolve eq110 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq110 (τ X1) (τ X0)
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq110
    | (have j0 := eq110 (τ X1) (τ X0)
       grind)
    | exact resolve eq110 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq497 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq509 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq508 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq512 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq502 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq502
    | (have j0 := eq502 X0 X1
       grind)
    | exact resolve eq502 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq515 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq512 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq512
    | (have j0 := eq512 X0 X1
       grind)
    | exact resolve eq512 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq517 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq515 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq515
    | (have j0 := eq515 X0 X1
       grind)
    | exact resolve eq515 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq518 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq517 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq517
    | (have j0 := eq517 X0 X1
       grind)
    | exact resolve eq517 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq519 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq518 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq518
    | (have j0 := eq518 X0 X1
       grind)
    | exact resolve eq518 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq520 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq519 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq519
    | (have j0 := eq519 X0 X1
       grind)
    | exact resolve eq519 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq546 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq111 (τ X1) (τ X0)
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq111
    | (have j0 := eq111 (τ X1) (τ X0)
       grind)
    | exact resolve eq111 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq559 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq546 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq546
    | (have j0 := eq546 X0 X1
       grind)
    | exact resolve eq546 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq562 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq559 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq559
    | (have j0 := eq559 X0 X1
       grind)
    | exact resolve eq559 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq564 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq562 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq562
    | (have j0 := eq562 X0 X1
       grind)
    | exact resolve eq562 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq565 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq564 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq564
    | (have j0 := eq564 X0 X1
       grind)
    | exact resolve eq564 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq566 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq565 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq565
    | (have j0 := eq565 X0 X1
       grind)
    | exact resolve eq565 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq567 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq566 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq566
    | (have j0 := eq566 X0 X1
       grind)
    | exact resolve eq566 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq616 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq102
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq102 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq617 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq616
  have eq11419 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq617
       grind)
    | exact superpose eq617 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq617
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq617
       grind)
    | exact resolve eq13 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11425 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq617
  have eq11427 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq11419
  have eq11430 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11427
       have r₂ := eq11425
       grind)
    | exact resolve eq11427 eq11425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11425 eq11427
  have eq11432 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11430
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq11430
    | exact resolve eq11430 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11430
  have eq148873 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq11432
       grind)
    | exact superpose eq11432 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq11432
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq11432
       grind)
    | exact resolve eq12 eq11432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11432
  have eq148890 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq148873
  have eq148903 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq148890
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq148890
    | exact resolve eq148890 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148890
  have eq168982 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq148903
       grind)
    | exact superpose eq148903 eq10
    | exact resolve eq10 eq148903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148903
  have eq169019 : y = (k y x) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq168982
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq168982
    | exact resolve eq168982 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168982
  have eq169020 : (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq520 y x
       grind)
    | (have r₁ := eq169019
       have r₂ := eq520 y x
       grind)
    | exact resolve eq169019 eq520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520 eq169019
  have eq169095 : (k y x) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq169020
       grind)
    | exact superpose eq169020 eq10
    | exact resolve eq10 eq169020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169020
  have eq169180 : x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq169095
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq169095
    | exact resolve eq169095 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169095
  have eq169181 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq567 y x
       grind)
    | (have r₁ := eq169180
       have r₂ := eq567 y x
       grind)
    | exact resolve eq169180 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567 eq169180
  have eq169248 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq169181
       grind)
    | exact superpose eq169181 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq169181
       grind)
    | exact resolve eq13 eq169181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169252 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq509 x y
       have i₂ := eq169181
       grind)
    | exact superpose eq169181 eq509
    | exact resolve eq509 eq169181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq169260 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq169262 : x = y ∨ x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq169248
  have eq169263 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq169262
       have r₂ := eq169260
       grind)
    | exact resolve eq169262 eq169260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169262
  have eq169593 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq111 x y
       have i₂ := eq169263
       grind)
    | exact superpose eq169263 eq111
    | (have j0 := eq111 x y
       grind)
    | exact resolve eq111 eq169263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq169731 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq169593
  have eq169771 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq52 (σ y) (σ y)
       have i₂ := eq169252
       grind)
    | exact superpose eq169252 eq52
    | exact resolve eq52 eq169252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq169252
  have eq169787 : (σ y) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq169771
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq169771
    | exact resolve eq169771 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169771
  have eq169842 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (k (k y y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq15 (k y y) X0
       have i₂ := eq169787
       grind)
    | exact superpose eq169787 eq15
    | exact resolve eq15 eq169787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169853 : ∀ X0 : G, (τ (k (σ y) X0)) = (k (k y y) (τ X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq32 (k y y) X0
       have i₂ := eq169787
       grind)
    | exact superpose eq169787 eq32
    | exact resolve eq32 eq169787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169787
  have eq170054 : ∀ X0 : G, (k y (τ X0)) = (k (k y y) (τ X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq169853 X0
       have i₂ := eq32 y X0
       grind)
    | exact superpose eq32 eq169853
    | exact resolve eq169853 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq169853
  have eq170065 : ∀ X0 : G, (σ (k y X0)) = (σ (k (k y y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq169842 X0
       have i₂ := eq15 y X0
       grind)
    | exact superpose eq15 eq169842
    | exact resolve eq169842 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169842
  have eq171018 : ∀ X0 : G, (k y X0) = (k (k y y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq170054 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq170054
    | exact resolve eq170054 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170054
  have eq173099 : ∀ X0 X1 : G, (k (τ X1) (k (k y y) X0)) = (τ (k X1 (σ (k y X0)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (k (k y y) X0)
       have i₂ := eq170065 X0
       grind)
    | exact superpose eq170065 eq24
    | exact resolve eq24 eq170065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173229 : ∀ X0 X1 : G, (k (τ X1) (k (k y y) X0)) = (k (τ X1) (k y X0)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq173099 X0 X1
       have i₂ := eq24 X1 (k y X0)
       grind)
    | exact superpose eq24 eq173099
    | exact resolve eq173099 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq173099
  have eq188967 : ∀ X0 X1 : G, (k X0 (k y X1)) = (k X0 (k (k y y) X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq173229 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq173229
    | exact resolve eq173229 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173229
  have eq189499 : ∀ X0 : G, (k (k y y) (k y X0)) = (k y (k (k y y) X0)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq171018 (k (k y y) X0)
       have i₂ := eq188967 (k y y) X0
       grind)
    | exact superpose eq188967 eq171018
    | exact resolve eq171018 eq188967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171018
  have eq189567 : ∀ X0 : G, (k (k y y) (k y X0)) = (k y (k (k y y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq189499 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189499
  have eq201113 : (k (k y y) x) = (k y (k (k y y) x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq189567 x
       have i₂ := eq169263
       grind)
    | exact superpose eq169263 eq189567
    | exact resolve eq189567 eq169263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189567
  have eq201327 : (k (k y y) x) = (k y (k (k y y) x)) ∨ x = (M.op x y) := by grind
  clear eq201113
  have eq201465 : (k y (k y x)) = (k (k y y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq188967 y x
       have i₂ := eq201327
       grind)
    | exact superpose eq201327 eq188967
    | exact resolve eq188967 eq201327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188967 eq201327
  have eq201466 : (k y (k y x)) = (k (k y y) x) ∨ x = (M.op x y) := by grind
  clear eq201465
  have eq201597 : (σ (k y x)) = (σ (k y (k y x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq170065 x
       have i₂ := eq201466
       grind)
    | exact superpose eq201466 eq170065
    | exact resolve eq170065 eq201466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170065 eq201466
  have eq201645 : (σ (k y x)) = (σ (k y (k y x))) ∨ x = (M.op x y) := by grind
  clear eq201597
  have eq202167 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq201645
       have i₂ := eq169263
       grind)
    | exact superpose eq169263 eq201645
    | exact resolve eq201645 eq169263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169263 eq201645
  have eq202246 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
  clear eq202167
  have eq237694 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq169731
       grind)
    | exact superpose eq169731 eq16
    | exact resolve eq16 eq169731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169731
  have eq237713 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq237694
       have i₂ := eq169181
       grind)
    | exact superpose eq169181 eq237694
    | exact resolve eq237694 eq169181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237694
  have eq237718 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq237713
  have eq237720 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq237718
       have r₂ := eq169260
       grind)
    | exact resolve eq237718 eq169260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237718
  have eq237724 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq237720
       grind)
    | exact superpose eq237720 eq16
    | exact resolve eq16 eq237720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237758 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq237720
       grind)
    | exact superpose eq237720 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq237720
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq237720
       grind)
    | exact resolve eq12 eq237720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237720
  have eq237878 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq237758
  have eq237994 : (σ y) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq237878
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq237878
    | exact resolve eq237878 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237878
  have eq238567 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq237724
       have i₂ := eq169181
       grind)
    | exact superpose eq169181 eq237724
    | exact resolve eq237724 eq169181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169181 eq237724
  have eq238577 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq238567
       have r₂ := eq169260
       grind)
    | exact resolve eq238567 eq169260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169260 eq238567
  have eq238735 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq202246
       have i₂ := eq237994
       grind)
    | exact superpose eq237994 eq202246
    | exact resolve eq202246 eq237994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202246
  have eq238777 : (k y x) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq237994
       grind)
    | exact superpose eq237994 eq10
    | exact resolve eq10 eq237994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237994
  have eq238907 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq238735
  have eq238937 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq238777
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq238777
    | exact resolve eq238777 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238777
  have eq238938 : x = (M.op x y) := by
    first
    | (have r₁ := eq238907
       have r₂ := eq238577
       grind)
    | exact resolve eq238907 eq238577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238577 eq238907
  have eq238942 : y = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq238937
       have r₂ := eq12 y x
       grind)
    | exact resolve eq238937 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238937
  have eq239155 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq110 x y
       have i₂ := eq238942
       grind)
    | exact superpose eq238942 eq110
    | (have j0 := eq110 x y
       grind)
    | exact resolve eq110 eq238942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq239241 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq239155
  have eq251088 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq239241
       grind)
    | exact superpose eq239241 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq239241
       grind)
    | exact resolve eq13 eq239241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251100 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq239241
  have eq251102 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq251088
  have eq251109 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq251102
       have r₂ := eq251100
       grind)
    | exact resolve eq251102 eq251100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251102
  have eq251111 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq251109
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq251109
    | exact resolve eq251109 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251109
  have eq251112 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq251111
       have i₂ := eq238942
       grind)
    | exact superpose eq238942 eq251111
    | exact resolve eq251111 eq238942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238942 eq251111
  have eq251113 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq251112
       have r₂ := eq251100
       grind)
    | exact resolve eq251112 eq251100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251100 eq251112
  have eq251118 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq251113
       grind)
    | exact superpose eq251113 eq16
    | exact resolve eq16 eq251113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251113
  have eq251482 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq251118
       have i₂ := eq238938
       grind)
    | exact superpose eq238938 eq251118
    | exact resolve eq251118 eq238938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238938 eq251118
  have eq251483 : False := by grind
  exact eq251483

/-- `Equation333`: `x ◇ y = y ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then Y else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_y_y_pyx_Equation333 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law333 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law333.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X1)
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq21 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq43 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq45 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq46 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq45 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 (M.op X0 X1) (M.op X0 X1)
       grind)
    | (have r₁ := eq12 (M.op X0 X1) (M.op X0 X1)
       have r₂ := eq18 X0 X1
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq98 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq46
    | exact resolve eq46 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq46 (τ X1) X0
       grind)
    | exact superpose eq46 eq20
    | (have j1 := eq46 (τ X1) X0
       grind)
    | exact resolve eq20 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq46
  have eq199 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 X0
       have i₂ := eq14 X0 (σ X0)
       grind)
    | (have i₁ := eq40 X0 X1
       have i₂ := eq14 (M.op (σ X0) (σ X1)) X1
       grind)
    | exact superpose eq14 eq40
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq40 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq40 X0 X1
       grind)
    | exact superpose eq40 eq10
    | (have j1 := eq40 X0 X1
       grind)
    | exact resolve eq10 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq40 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq240 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq238 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq245 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq199 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq403 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq240 (M.op X0 X1)
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq240
    | (have j0 := eq240 (M.op X0 X1)
       grind)
    | exact resolve eq240 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq407 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq240 (τ X0)
       have i₂ := eq21 X0 (τ X0)
       grind)
    | exact superpose eq21 eq240
    | (have j0 := eq240 (τ X0)
       grind)
    | exact resolve eq240 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq409 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq403 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq412 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq407 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq407
    | (have j0 := eq407 X0
       grind)
    | exact resolve eq407 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq415 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq412 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq412
    | (have j0 := eq412 X0
       grind)
    | exact resolve eq412 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq426 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq415 (τ X0)
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq415
    | (have j0 := eq415 (τ X0)
       grind)
    | exact resolve eq415 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq432 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq105
    | exact resolve eq105 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq462 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq432 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq432
    | (have j0 := eq432 X0 X1
       grind)
    | exact resolve eq432 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq596 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq98 y x
       grind)
    | exact superpose eq98 eq16
    | (have j1 := eq98 y x
       grind)
    | exact resolve eq16 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq1572 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq239 (τ X1) (τ X0)
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq239
    | (have j0 := eq239 (τ X1) (τ X0)
       grind)
    | exact resolve eq239 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq1594 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1572 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1572
    | (have j0 := eq1572 X0 X1
       grind)
    | exact resolve eq1572 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1572
  have eq1598 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1594 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1594
    | (have j0 := eq1594 X0 X1
       grind)
    | exact resolve eq1594 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594
  have eq1600 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1598 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1598
    | (have j0 := eq1598 X0 X1
       grind)
    | exact resolve eq1598 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1598
  have eq1601 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1600 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1600
    | (have j0 := eq1600 X0 X1
       grind)
    | exact resolve eq1600 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1600
  have eq1602 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1601 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1601
    | (have j0 := eq1601 X0 X1
       grind)
    | exact resolve eq1601 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601
  have eq1603 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1602 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1602
    | (have j0 := eq1602 X0 X1
       grind)
    | exact resolve eq1602 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1602
  have eq2365 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq219 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq2729 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq245 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq245
    | (have j0 := eq245 X1 (τ X0)
       grind)
    | exact resolve eq245 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq2887 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2729 X0 X1
       have i₂ := eq21 X0 (τ X0)
       grind)
    | exact superpose eq21 eq2729
    | (have j0 := eq2729 X0 X1
       grind)
    | exact resolve eq2729 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq2729
  have eq2905 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X0 X0) = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2887 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2887
    | (have j0 := eq2887 X0 X1
       grind)
    | exact resolve eq2887 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2887
  have eq3838 : ∀ X0 X1 : G, (τ (M.op X0 X1)) ≠ (τ (M.op X0 X1)) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq426 (M.op X0 X1)
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq426
    | (have j0 := eq426 (M.op X0 X1)
       grind)
    | exact resolve eq426 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq3848 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3838 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3838
  have eq6233 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq596
       have i₂ := eq462 y x
       grind)
    | exact superpose eq462 eq596
    | (have j1 := eq462 y x
       grind)
    | (have r₁ := eq596
       have r₂ := eq462 y x
       grind)
    | exact resolve eq596 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462 eq596
  have eq6235 : (σ (M.op x y)) = (σ x) ∨ x = (k y x) := by grind
  clear eq6233
  have eq6895 : (M.op x y) = (τ (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq6235
       grind)
    | exact superpose eq6235 eq10
    | exact resolve eq10 eq6235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6235
  have eq6970 : x = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq6895
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6895
    | exact resolve eq6895 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6895
  have eq6971 : x = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq6970
       have r₂ := eq12 y x
       grind)
    | exact resolve eq6970 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6970
  have eq7321 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq43 y x
       have i₂ := eq6971
       grind)
    | exact superpose eq6971 eq43
    | (have j0 := eq43 y x
       grind)
    | exact resolve eq43 eq6971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq7325 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq239 x y
       have i₂ := eq6971
       grind)
    | exact superpose eq6971 eq239
    | (have j0 := eq239 x y
       grind)
    | exact resolve eq239 eq6971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq7327 : x ≠ x ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1603 y x
       have i₂ := eq6971
       grind)
    | exact superpose eq6971 eq1603
    | (have j0 := eq1603 y x
       grind)
    | (have r₁ := eq1603 y x
       have r₂ := eq6971
       grind)
    | exact resolve eq1603 eq6971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1603
  have eq7328 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq7327
  have eq7329 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq7325
  have eq7331 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq7321
  have eq7811 : y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18 x y
       have i₂ := eq7328
       grind)
    | exact superpose eq7328 eq18
    | exact resolve eq18 eq7328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq7328
  have eq9100 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq7331
  have eq10659 : y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9 x x
       have i₂ := eq7811
       grind)
    | exact superpose eq7811 eq9
    | exact resolve eq9 eq7811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7811
  have eq20472 : x = (M.op x y) ∨ y = (k x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6971
       have i₂ := eq2905 x y
       grind)
    | exact superpose eq2905 eq6971
    | (have j1 := eq2905 x y
       grind)
    | exact resolve eq6971 eq2905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2905
  have eq20616 : x = (M.op x y) ∨ y = (k x x) ∨ x = y := by grind
  clear eq20472
  have eq20696 : y = (k x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20616
       have r₂ := eq9100
       grind)
    | exact resolve eq20616 eq9100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20616
  have eq26038 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3848 (σ x) (σ y)
       have i₂ := eq7329
       grind)
    | exact superpose eq7329 eq3848
    | exact resolve eq3848 eq7329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3848 eq7329
  have eq26043 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq26038
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq26038
    | exact resolve eq26038 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26038
  have eq26869 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9 (σ x) (σ x)
       have i₂ := eq26043
       grind)
    | exact superpose eq26043 eq9
    | exact resolve eq9 eq26043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26043
  have eq27325 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26869
       grind)
    | exact superpose eq26869 eq16
    | exact resolve eq16 eq26869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26869
  have eq27755 : (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq27325
       have i₂ := eq10659
       grind)
    | exact superpose eq10659 eq27325
    | exact resolve eq27325 eq10659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10659 eq27325
  have eq27761 : (σ y) ≠ (σ y) ∨ x = (M.op x x) := by grind
  clear eq27755
  have eq27762 : x = (M.op x x) := by grind
  clear eq27761
  have eq28124 : x = (k x x) := by
    first
    | (have i₁ := eq67 x x
       have i₂ := eq27762
       grind)
    | exact superpose eq27762 eq67
    | exact resolve eq67 eq27762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq28125 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq409 x x
       have i₂ := eq27762
       grind)
    | exact superpose eq27762 eq409
    | exact resolve eq409 eq27762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq28441 : x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20696
       have i₂ := eq28124
       grind)
    | exact superpose eq28124 eq20696
    | exact resolve eq20696 eq28124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20696 eq28124
  have eq28503 : x = (M.op x y) := by
    first
    | (have r₁ := eq28441
       have r₂ := eq9100
       grind)
    | exact resolve eq28441 eq9100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9100 eq28441
  have eq35406 : (σ x) ≠ (σ x) ∨ y = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2365 x y
       have i₂ := eq6971
       grind)
    | exact superpose eq6971 eq2365
    | (have j0 := eq2365 x y
       grind)
    | exact resolve eq2365 eq6971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2365 eq6971
  have eq35479 : y = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq35406
  have eq35524 : y = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35479
       have i₂ := eq28125
       grind)
    | exact superpose eq28125 eq35479
    | exact resolve eq35479 eq28125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35479
  have eq35549 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq35524
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq35524
    | exact resolve eq35524 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35524
  have eq35605 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq35549
       grind)
    | exact superpose eq35549 eq16
    | exact resolve eq16 eq35549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35549
  have eq35636 : (σ x) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq35605
       have i₂ := eq28503
       grind)
    | exact superpose eq28503 eq35605
    | exact resolve eq35605 eq28503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28503 eq35605
  have eq35637 : x = y := by grind
  clear eq35636
  have eq35914 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35637
       grind)
    | exact superpose eq35637 eq16
    | exact resolve eq16 eq35637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35637
  have eq35968 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq35914
       have i₂ := eq27762
       grind)
    | exact superpose eq27762 eq35914
    | exact resolve eq35914 eq27762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27762 eq35914
  have eq35969 : False := by grind
  exact eq35969

/-- `Equation3342`: `x ◇ y = y ◇ (x ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pxx_x_pxy_Equation3342 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3342 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3342.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq36 (σ X0)
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq40
    | exact resolve eq40 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq40
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X1) (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq103 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq106 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq103 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq103 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq103 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq103 X0 X1
       have r₂ := eq14 (M.op X0 X1) (M.op X0 X0)
       grind)
    | exact resolve eq103 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq251 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq106 (σ X0) (σ X1)
       grind)
    | exact superpose eq106 eq15
    | (have j1 := eq106 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq106 (τ X0) X1
       grind)
    | exact superpose eq106 eq18
    | (have j1 := eq106 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq106
  have eq930 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq253 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq253
    | exact resolve eq253 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq968 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq930 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq930
    | (have j0 := eq930 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq930 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq3176 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq251 x y
       grind)
    | exact superpose eq251 eq16
    | (have j1 := eq251 x y
       grind)
    | exact resolve eq16 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq3246 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3176
       have i₂ := eq968 x y
       grind)
    | exact superpose eq968 eq3176
    | (have j1 := eq968 (σ x) (σ y)
       grind)
    | (have r₁ := eq3176
       have r₂ := eq968 x y
       grind)
    | (have r₁ := eq3176
       have r₂ := eq968 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq3176
       have r₂ := eq968 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3176 eq968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968 eq3176
  have eq3247 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq3246
  have eq3354 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3247
       grind)
    | exact superpose eq3247 eq10
    | exact resolve eq10 eq3247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3247
  have eq3403 : x = y ∨ x = y := by
    first
    | (have i₁ := eq3354
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3354
    | exact resolve eq3354 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3354
  have eq3404 : x = y := by grind
  clear eq3403
  have eq3540 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3404
       grind)
    | exact superpose eq3404 eq16
    | exact resolve eq16 eq3404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3404
  have eq3541 : False := by grind
  exact eq3541

/-- `Equation3342`: `x ◇ y = y ◇ (x ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pyx_x_pyx_Equation3342 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3342 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3342.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq36 (σ X0)
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq40
    | exact resolve eq40 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq40
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X1) (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq64 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq72 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq64 (σ X1) (σ X0)
       grind)
    | exact superpose eq64 eq15
    | (have j1 := eq64 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq64 (τ X1) X0
       grind)
    | exact superpose eq64 eq18
    | (have j1 := eq64 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq64
  have eq365 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq73
    | exact resolve eq73 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq387 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq365 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq365
    | (have j0 := eq365 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq365 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq892 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq72 x y
       grind)
    | exact superpose eq72 eq16
    | (have j1 := eq72 x y
       grind)
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq923 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq892
       have i₂ := eq387 y x
       grind)
    | exact superpose eq387 eq892
    | (have j1 := eq387 (σ x) (σ y)
       grind)
    | (have r₁ := eq892
       have r₂ := eq387 y x
       grind)
    | (have r₁ := eq892
       have r₂ := eq387 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq892
       have r₂ := eq387 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq892 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387 eq892
  have eq924 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq923
  have eq962 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq924
       grind)
    | exact superpose eq924 eq10
    | exact resolve eq10 eq924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq998 : x = y ∨ x = y := by
    first
    | (have i₁ := eq962
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq962
    | exact resolve eq962 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq999 : x = y := by grind
  clear eq998
  have eq1110 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq999
       grind)
    | exact superpose eq999 eq16
    | exact resolve eq16 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999
  have eq1111 : False := by grind
  exact eq1111

/-- `Equation3342`: `x ◇ y = y ◇ (x ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxx_x_pyx_Equation3342 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3342 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3342.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq36 (σ X0)
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq45 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq45
    | exact resolve eq45 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq45
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq116 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq119 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq116 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq116 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq116 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq116 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq116 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq263 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq119 (σ X1) (σ X0)
       grind)
    | exact superpose eq119 eq15
    | (have j1 := eq119 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq119 (τ X1) X0
       grind)
    | exact superpose eq119 eq18
    | (have j1 := eq119 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq119
  have eq870 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq265 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq265
    | exact resolve eq265 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq906 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq870 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq870
    | (have j0 := eq870 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq870 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq2980 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq263 x y
       grind)
    | exact superpose eq263 eq16
    | (have j1 := eq263 x y
       grind)
    | exact resolve eq16 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq3081 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2980
       have i₂ := eq906 y x
       grind)
    | exact superpose eq906 eq2980
    | (have j1 := eq906 (σ x) (σ y)
       grind)
    | (have r₁ := eq2980
       have r₂ := eq906 y x
       grind)
    | (have r₁ := eq2980
       have r₂ := eq906 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2980
       have r₂ := eq906 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2980 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906 eq2980
  have eq3082 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq3081
  have eq3369 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3082
       grind)
    | exact superpose eq3082 eq10
    | exact resolve eq10 eq3082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3082
  have eq3418 : x = y ∨ x = y := by
    first
    | (have i₁ := eq3369
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3369
    | exact resolve eq3369 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3369
  have eq3419 : x = y := by grind
  clear eq3418
  have eq3743 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3419
       grind)
    | exact superpose eq3419 eq16
    | exact resolve eq16 eq3419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3419
  have eq3744 : False := by grind
  exact eq3744
