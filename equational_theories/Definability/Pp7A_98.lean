import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,X) = m(X,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pxx_pxy_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq30 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
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
  have eq55 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X2 (M.op (M.op X0 X1) X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) X1) (M.op X2 (M.op (M.op X0 X1) X1)) X2
       have i₂ := eq9 X1 (M.op X2 (M.op (M.op X0 X1) X1)) X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (k (k (M.op X0 X0) X0) (M.op X0 X0)) = (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) := by
    intro X0
    grind
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op (k (M.op X0 X0) X0) (M.op X0 X0)))) := by
    intro X0 X1
    grind
  have eq232 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (k (M.op X0 X0) X0) (M.op X0 X0))) (M.op (k (M.op X0 X0) X0) (M.op X0 X0))) = (M.op (M.op X0 X0) (M.op (k (M.op X0 X0) X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1 (M.op (k (M.op X0 X0) X0) (M.op X0 X0)) (M.op X1 (M.op (k (M.op X0 X0) X0) (M.op X0 X0)))
       have i₂ := eq57 X0 (M.op X1 (M.op (k (M.op X0 X0) X0) (M.op X0 X0)))
       grind)
    | exact superpose eq57 eq55
    | exact resolve eq55 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq339 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq362 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq361 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq394 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq362
  have eq448 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq394 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq512 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq448 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq538 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 X2 X1 X0
       have i₂ := eq9 X1 X1 X0
       grind)
    | exact superpose eq9 eq54
    | exact resolve eq54 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq572 : ∀ X0 X2 X3 : G, (M.op X3 (M.op X3 X2)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq538 x X2 X0
       have i₂ := eq538 x X2 X3
       grind)
    | exact superpose eq538 eq538
    | exact resolve eq538 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq580 : ∀ X0 X2 : G, (M.op X2 (M.op X0 (M.op X0 X2))) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X2 X2 x
       have i₂ := eq538 x X2 X0
       grind)
    | exact superpose eq538 eq9
    | exact resolve eq9 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X1 (M.op (M.op X2 X1) X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X0 X1 (M.op X0 X1)
       have i₂ := eq538 X2 X1 (M.op X0 X1)
       grind)
    | exact superpose eq538 eq55
    | exact resolve eq55 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq596 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X2 X1) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq589 X0 X1 X2
       have i₂ := eq55 X2 X1 X1
       grind)
    | exact superpose eq55 eq589
    | exact resolve eq589 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq624 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq580 X0 (M.op X0 X0)
       have i₂ := eq580 X0 X0
       grind)
    | exact superpose eq580 eq580
    | exact resolve eq580 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq629 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X2 (M.op X0 (M.op X0 X2)) X2
       have i₂ := eq580 X0 X2
       grind)
    | exact superpose eq580 eq55
    | exact resolve eq55 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq632 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq629 X2 X0 X2
       have i₂ := eq580 X0 X2
       grind)
    | (have i₁ := eq629 X0 X1 X2
       have i₂ := eq580 X0 (M.op X0 (M.op X1 (M.op X1 X0)))
       grind)
    | exact superpose eq580 eq629
    | exact resolve eq629 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq642 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (k (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq648 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq624 X0
       grind)
    | exact superpose eq624 eq9
    | exact resolve eq9 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq653 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq538 X1 X0 (M.op X0 X0)
       have i₂ := eq624 X0
       grind)
    | exact superpose eq624 eq538
    | exact resolve eq538 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq654 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq580 (M.op X0 X0) X0
       have i₂ := eq624 X0
       grind)
    | exact superpose eq624 eq580
    | exact resolve eq580 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq663 : ∀ X0 : G, (M.op X0 (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    grind
  clear eq654
  have eq664 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op (M.op X1 X0) X0)) := by
    intro X0 X1
    grind
  clear eq653
  have eq678 : ∀ X0 : G, (M.op (M.op X0 X0) (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    grind
  have eq683 : ∀ X0 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X2 (M.op X0 X0)) (M.op X0 X0))) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq538 X2 (M.op X0 X0) x
       have i₂ := eq648 X0 x
       grind)
    | exact superpose eq648 eq538
    | exact resolve eq538 eq648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq695 : ∀ X0 : G, (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq683 X0 x
       have i₂ := eq664 (M.op X0 X0) x
       grind)
    | exact superpose eq664 eq683
    | exact resolve eq683 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664 eq683
  have eq699 : ∀ X0 : G, (k (k (M.op X0 X0) X0) (M.op X0 X0)) = X0 := by
    intro X0
    grind
  clear eq695
  have eq712 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op X1 (M.op X1 (M.op X0 (k (M.op X0 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (M.op X0 X0) X0) X1 X0
       have i₂ := eq663 X0
       grind)
    | exact superpose eq663 eq9
    | exact resolve eq9 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq722 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq712 X0 X1
       have i₂ := eq663 X0
       grind)
    | exact superpose eq663 eq712
    | exact resolve eq712 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663 eq712
  have eq767 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq572 X1 (M.op X1 (M.op X0 X0)) X2
       have i₂ := eq648 X0 X1
       grind)
    | exact superpose eq648 eq572
    | exact resolve eq572 eq648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq773 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq572 X0 (M.op X1 (M.op X1 X0)) X2
       have i₂ := eq580 X1 X0
       grind)
    | exact superpose eq580 eq572
    | exact resolve eq572 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq872 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X1 (M.op X1 X0))) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq596 X2 (M.op X1 (M.op X1 X0)) X0
       have i₂ := eq580 X1 X0
       grind)
    | exact superpose eq580 eq596
    | exact resolve eq596 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq898 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq624 X0
       have i₂ := eq596 X0 X0 X1
       grind)
    | (have i₁ := eq624 X0
       have i₂ := eq596 X1 X0 X0
       grind)
    | exact superpose eq596 eq624
    | exact resolve eq624 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq916 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op (k (M.op X2 X2) X2) (M.op X2 X2))) (M.op (M.op X1 (M.op (k (M.op X2 X2) X2) (M.op X2 X2))) (M.op (k (M.op X2 X2) X2) (M.op X2 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X2 (M.op X0 (M.op (k (M.op X2 X2) X2) (M.op X2 X2)))
       have i₂ := eq596 X0 (M.op (k (M.op X2 X2) X2) (M.op X2 X2)) X1
       grind)
    | (have i₁ := eq57 X2 (M.op X0 (M.op (k (M.op X2 X2) X2) (M.op X2 X2)))
       have i₂ := eq596 X1 (M.op (k (M.op X2 X2) X2) (M.op X2 X2)) X0
       grind)
    | exact superpose eq596 eq57
    | exact resolve eq57 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq596
  have eq917 : ∀ X0 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op (k (M.op X2 X2) X2) (M.op X2 X2))) (M.op (M.op X2 X2) (M.op (k (M.op X2 X2) X2) (M.op X2 X2)))) := by
    intro X0 X2
    first
    | (have i₁ := eq916 X0 x X2
       have i₂ := eq232 X2 x
       grind)
    | exact superpose eq232 eq916
    | exact resolve eq916 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232 eq916
  have eq930 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq872 X0 X1 x
       have i₂ := eq898 (M.op X1 (M.op X1 X0)) x
       grind)
    | exact superpose eq898 eq872
    | exact resolve eq872 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872 eq898
  have eq963 : ∀ X0 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (k (M.op X2 X2) X2)) (M.op (M.op X2 X2) (k (M.op X2 X2) X2))) := by
    intro X0 X2
    first
    | (have i₁ := eq917 X0 X0
       have i₂ := eq642 X0
       grind)
    | exact superpose eq642 eq917
    | exact resolve eq917 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642 eq917
  have eq972 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq930 X0 X1
       have i₂ := eq580 X1 X0
       grind)
    | (have i₁ := eq930 X0 X1
       have i₂ := eq580 X0 (M.op X0 (M.op X1 (M.op X1 X0)))
       grind)
    | exact superpose eq580 eq930
    | exact resolve eq930 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580 eq930
  have eq985 : ∀ X0 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (k (M.op X2 X2) X2)) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq963 X0 X2
       have i₂ := eq678 X2
       grind)
    | exact superpose eq678 eq963
    | exact resolve eq963 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678 eq963
  have eq1043 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq632 (M.op X1 (M.op X0 X0)) X2 X1
       have i₂ := eq648 X0 X1
       grind)
    | exact superpose eq648 eq632
    | exact resolve eq632 eq648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1091 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1043 X0 X1 x
       have i₂ := eq767 X0 X1 x
       grind)
    | exact superpose eq767 eq1043
    | exact resolve eq1043 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767 eq1043
  have eq1282 : ∀ X0 : G, (k (k (k (M.op X0 X0) X0) (M.op X0 X0)) (k (M.op X0 X0) X0)) = (M.op (k (k (M.op X0 X0) X0) (M.op X0 X0)) (k (k (M.op X0 X0) X0) (M.op X0 X0))) := by
    intro X0
    grind
  clear eq56
  have eq1314 : ∀ X0 : G, (M.op X0 X0) = (k X0 (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq1282 X0
       have i₂ := eq699 X0
       grind)
    | exact superpose eq699 eq1282
    | exact resolve eq1282 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699 eq1282
  have eq1371 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq722 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq722 X0 X1
       have i₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact superpose eq14 eq722
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq722 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1388 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1314 X0
       have i₂ := eq722 X0 X1
       grind)
    | exact superpose eq722 eq1314
    | exact resolve eq1314 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722 eq1314
  have eq1410 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1371 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371
  have eq1452 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1091 (M.op X0 X1) X0
       have i₂ := eq632 X1 X0 X0
       grind)
    | exact superpose eq632 eq1091
    | exact resolve eq1091 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq1454 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq648 X0 X1
       have i₂ := eq1091 X0 X1
       grind)
    | (have i₁ := eq648 X0 X0
       have i₂ := eq1091 X0 X0
       grind)
    | exact superpose eq1091 eq648
    | exact resolve eq648 eq1091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
  have eq2109 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X0 (M.op X2 (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq773 X1 X0 X0
       have i₂ := eq572 X2 (M.op X0 X1) X0
       grind)
    | (have i₁ := eq773 X1 X0 X0
       have i₂ := eq572 X0 (M.op X0 X1) X2
       grind)
    | exact superpose eq572 eq773
    | exact resolve eq773 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq773
  have eq2688 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (k X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq985 X0 (M.op X1 (M.op X1 X0))
       have i₂ := eq972 X0 X1
       grind)
    | exact superpose eq972 eq985
    | exact resolve eq985 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972 eq985
  have eq2739 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X0 X0)) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2688 X0 X1 X2
       have i₂ := eq1388 X0 X1
       grind)
    | exact superpose eq1388 eq2688
    | exact resolve eq2688 eq1388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1388 eq2688
  have eq3300 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X2 (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2739 (M.op X0 X1) X2 X0
       have i₂ := eq1452 X0 X1
       grind)
    | exact superpose eq1452 eq2739
    | exact resolve eq2739 eq1452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452 eq2739
  have eq7736 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq512 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq7765 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7736 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq7736
    | exact resolve eq7736 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7766 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq7736 (τ X0)
       have i₂ := eq30 X0 X0
       grind)
    | exact superpose eq30 eq7736
    | exact resolve eq7736 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq7775 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7766 X0
       have i₂ := eq7736 X0
       grind)
    | exact superpose eq7736 eq7766
    | exact resolve eq7766 eq7736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7766
  have eq7776 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7765 X0
       have i₂ := eq7736 X0
       grind)
    | exact superpose eq7736 eq7765
    | exact resolve eq7765 eq7736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7736 eq7765
  have eq8123 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq648 (τ X0) X1
       have i₂ := eq7775 X0
       grind)
    | exact superpose eq7775 eq648
    | exact resolve eq648 eq7775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7775
  have eq25888 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X0 (M.op X2 (M.op X2 (M.op X0 X0)))) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2109 X0 X1 X2
       have i₂ := eq1410 X0 X1
       grind)
    | (have i₁ := eq2109 X0 X0 X2
       have i₂ := eq1410 X0 X1
       grind)
    | exact superpose eq1410 eq2109
    | (have j1 := eq1410 X0 X1
       grind)
    | exact resolve eq2109 eq1410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410 eq2109
  have eq26034 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25888 X0 X1 x
       have i₂ := eq3300 X0 X0 x
       grind)
    | exact superpose eq3300 eq25888
    | (have j0 := eq25888 X0 X1 x
       grind)
    | exact resolve eq25888 eq3300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3300 eq25888
  have eq29598 : ∀ X0 X1 X2 : G, (τ X0) = (M.op X2 (M.op X2 (τ (M.op X1 X1)))) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8123 X0 X2
       have i₂ := eq26034 X0 X1
       grind)
    | (have i₁ := eq8123 X1 X1
       have i₂ := eq26034 X0 X1
       grind)
    | exact superpose eq26034 eq8123
    | (have j1 := eq26034 X0 X1
       grind)
    | exact resolve eq8123 eq26034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29648 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1454 X0 X0
       have i₂ := eq26034 X0 X1
       grind)
    | (have i₁ := eq1454 X1 X1
       have i₂ := eq26034 X0 X1
       grind)
    | exact superpose eq26034 eq1454
    | (have j1 := eq26034 X0 X1
       grind)
    | exact resolve eq1454 eq26034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1454 eq26034
  have eq29715 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29648 X0 X1
       have i₂ := eq648 X1 X0
       grind)
    | exact superpose eq648 eq29648
    | (have j0 := eq29648 X0 X1
       grind)
    | exact resolve eq29648 eq648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648 eq29648
  have eq29725 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29598 X0 X1 x
       have i₂ := eq8123 X1 x
       grind)
    | exact superpose eq8123 eq29598
    | (have j0 := eq29598 X0 X1 x
       grind)
    | exact resolve eq29598 eq8123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8123 eq29598
  have eq29947 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29725 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq29725
    | (have j0 := eq29725 (σ X0) (σ X1)
       grind)
    | exact resolve eq29725 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29725
  have eq29998 : ∀ X0 X1 : G, (τ (σ X0)) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29947 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq29947
    | (have j0 := eq29947 X0 X1
       grind)
    | exact resolve eq29947 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29947
  have eq30008 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29998 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29998
    | (have j0 := eq29998 X0 X1
       grind)
    | exact resolve eq29998 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29998
  have eq30349 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq30008 y x
       grind)
    | exact superpose eq30008 eq16
    | (have j1 := eq30008 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq30008 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq30008 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq30008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30008
  have eq30463 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq30349
       have i₂ := eq29715 y x
       grind)
    | exact superpose eq29715 eq30349
    | (have j1 := eq29715 x y
       grind)
    | (have r₁ := eq30349
       have r₂ := eq29715 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq30349
       have r₂ := eq29715 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq30349 eq29715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29715 eq30349
  have eq30468 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by grind
  clear eq30463
  have eq30469 : x = y := by grind
  clear eq30468
  have eq30475 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30469
       grind)
    | exact superpose eq30469 eq16
    | exact resolve eq16 eq30469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30469
  have eq30476 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq30475
       have i₂ := eq7776 x
       grind)
    | exact superpose eq7776 eq30475
    | (have r₁ := eq30475
       have r₂ := eq7776 x
       grind)
    | exact resolve eq30475 eq7776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7776 eq30475
  have eq30477 : False := by grind
  exact eq30477

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxx_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
    intro X0 X1 X2
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
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
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
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
  have eq70 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq85 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq70
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq70
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq85
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq85
    | exact resolve eq85 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq91
    | exact resolve eq91 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq92
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq92
    | exact resolve eq92 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq105 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq328 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq105 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq105
    | (have j0 := eq105 (σ X0)
       grind)
    | exact resolve eq105 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq105 x
       grind)
    | exact superpose eq105 eq44
    | (have j1 := eq105 x
       grind)
    | exact resolve eq44 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq403 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op (M.op X2 X0) X0)) = (M.op X0 (M.op (M.op X2 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq14 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq505 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X2 X0 X1
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq729 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq505 X1 x X3
       have i₂ := eq505 X1 x X0
       grind)
    | exact superpose eq505 eq505
    | exact resolve eq505 eq505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 x
       have i₂ := eq505 X1 x X0
       grind)
    | exact superpose eq505 eq14
    | exact resolve eq14 eq505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq751 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X0 (M.op X2 X0) X2
       have i₂ := eq505 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq505 eq54
    | exact resolve eq54 eq505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq756 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq751 X0 X1 X2
       have i₂ := eq54 X0 X0 X1
       grind)
    | exact superpose eq54 eq751
    | exact resolve eq751 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq770 : y = (M.op y (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq742 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq742
    | (have j0 := eq742 x y
       grind)
    | exact resolve eq742 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq771 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq742
    | (have j0 := eq742 (σ x) (σ y)
       grind)
    | exact resolve eq742 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq776 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq742 X0 (M.op X0 X0)
       have i₂ := eq742 X0 X0
       grind)
    | exact superpose eq742 eq742
    | exact resolve eq742 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq782 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op X0 (M.op X0 X1)) X1 X1
       have i₂ := eq742 X0 X1
       grind)
    | exact superpose eq742 eq54
    | exact resolve eq54 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq785 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq782 X1 X0 X2
       have i₂ := eq742 X0 X1
       grind)
    | exact superpose eq742 eq782
    | exact resolve eq782 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq877 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1 X0
       have i₂ := eq776 X0
       grind)
    | exact superpose eq776 eq54
    | exact resolve eq54 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq878 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq776 X0
       grind)
    | exact superpose eq776 eq14
    | exact resolve eq14 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1334 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq729 X0 (M.op X1 (M.op X1 X0)) X2
       have i₂ := eq742 X1 X0
       grind)
    | exact superpose eq742 eq729
    | exact resolve eq729 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1350 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq770 eq729
    | exact resolve eq729 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq1354 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq771 eq729
    | exact resolve eq729 eq771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729 eq771
  have eq1574 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq756 X0 X1 X0
       have i₂ := eq776 X0
       grind)
    | exact superpose eq776 eq756
    | exact resolve eq756 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756 eq776
  have eq3458 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq328 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq3526 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq403 X0 X1 X1
       have i₂ := eq1574 X0 X1
       grind)
    | exact superpose eq1574 eq403
    | exact resolve eq403 eq1574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq3527 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3526 X0 x
       have i₂ := eq1574 (M.op X0 X0) x
       grind)
    | exact superpose eq1574 eq3526
    | exact resolve eq3526 eq1574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1574 eq3526
  have eq3547 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0
    grind
  have eq3569 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3547 X0
       have i₂ := eq785 X0 X0 X0
       grind)
    | exact superpose eq785 eq3547
    | exact resolve eq3547 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3547
  have eq3589 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3569 (M.op X0 X0)
       have i₂ := eq3527 X0
       grind)
    | exact superpose eq3527 eq3569
    | exact resolve eq3569 eq3527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3527 eq3569
  have eq3601 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3589 X0
       have i₂ := eq785 X0 X0 X0
       grind)
    | exact superpose eq785 eq3589
    | exact resolve eq3589 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785 eq3589
  have eq19677 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op y y)) := by
    first
    | exact superpose eq1350 eq1334
    | exact resolve eq1334 eq1350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1350
  have eq19680 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq1354 eq1334
    | exact resolve eq1334 eq1354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334 eq1354
  have eq20066 : y = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq878 y x
       have i₂ := eq19677
       grind)
    | exact superpose eq19677 eq878
    | exact resolve eq878 eq19677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19677
  have eq20115 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq20066 eq877
    | exact resolve eq877 eq20066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20166 : y = (M.op x (M.op y (M.op x y))) := by
    first
    | exact superpose eq20115 eq20066
    | exact resolve eq20066 eq20115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20066 eq20115
  have eq20245 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq19680 eq878
    | exact resolve eq878 eq19680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878 eq19680
  have eq20505 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20245 eq877
    | exact resolve eq877 eq20245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877
  have eq20767 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq20505 eq20245
    | exact resolve eq20245 eq20505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20245 eq20505
  have eq23631 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq93 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23632 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq23631
    | exact resolve eq23631 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23631
  have eq23643 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq23632
       have r₂ := eq28
       grind)
    | exact resolve eq23632 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23632
  have eq23645 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq23643
    | exact resolve eq23643 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23643
  have eq23655 : (σ x) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23645 eq742
    | exact resolve eq742 eq23645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23645
  have eq23670 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20767 eq23655
    | exact resolve eq23655 eq20767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23655
  have eq23674 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq23670
  have eq23733 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq23674
    | exact resolve eq23674 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23674
  have eq24469 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23733 eq93
    | exact resolve eq93 eq23733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq23733
  have eq24477 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq24469
  have eq24479 : (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq24477
       have r₂ := eq28
       grind)
    | exact resolve eq24477 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24477
  have eq24744 : x = (M.op x (M.op y (M.op x y))) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq742 y x
       have i₂ := eq24479
       grind)
    | exact superpose eq24479 eq742
    | exact resolve eq742 eq24479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24479
  have eq24759 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20166 eq24744
    | exact resolve eq24744 eq20166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20166 eq24744
  have eq24763 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq24759
  have eq24822 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq24763
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24763
    | exact resolve eq24763 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24763
  have eq25347 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq24822
       grind)
    | exact superpose eq24822 eq70
    | exact resolve eq70 eq24822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq24822
  have eq25365 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq25347
    | exact resolve eq25347 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25347
  have eq25487 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq25365 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq25365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25490 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq25487
    | exact resolve eq25487 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25487
  have eq25501 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq25490
       have r₂ := eq28
       grind)
    | exact resolve eq25490 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25490
  have eq25503 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq25501
    | exact resolve eq25501 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25501
  have eq71491 : (σ x) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq25503 eq742
    | exact resolve eq742 eq25503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq25503
  have eq71510 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20767 eq71491
    | exact resolve eq71491 eq20767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20767 eq71491
  have eq71511 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq71510
  have eq72080 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq71511
  have eq72145 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq72080
    | exact resolve eq72080 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72080
  have eq73343 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq72145 eq25365
    | exact resolve eq25365 eq72145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25365 eq72145
  have eq73349 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq73343
  have eq73358 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq73349
       have r₂ := eq28
       grind)
    | exact resolve eq73349 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73349
  have eq73362 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq73358 eq30
    | exact resolve eq30 eq73358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq73358
  have eq73527 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq73362
    | exact resolve eq73362 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq73362
  have eq73528 : x = y := by grind
  clear eq73527
  have eq73529 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq73528
       grind)
    | exact superpose eq73528 eq19
    | exact resolve eq19 eq73528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq73530 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq73528
       grind)
    | exact superpose eq73528 eq25
    | exact resolve eq25 eq73528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq73528
  have eq73831 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq73530
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq73530
    | exact resolve eq73530 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73530
  have eq73835 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq73831 eq27
    | exact resolve eq27 eq73831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq73831
  have eq75062 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq332
       have i₂ := eq73529
       grind)
    | exact superpose eq73529 eq332
    | exact resolve eq332 eq73529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq75122 : (M.op x y) = (k x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq3601 x
       have i₂ := eq73529
       grind)
    | exact superpose eq73529 eq3601
    | exact resolve eq3601 eq73529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3601
  have eq75163 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq75062
    | exact resolve eq75062 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75062
  have eq76227 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq86599 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq75163 eq105
    | (have j0 := eq105 (σ x)
       grind)
    | exact resolve eq105 eq75163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq86600 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq73835 eq86599
    | exact resolve eq86599 eq73835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86599
  have eq86612 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq86600
       have r₂ := eq28
       grind)
    | exact resolve eq86600 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86600
  have eq86618 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq73835 eq86612
    | exact resolve eq86612 eq73835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86612
  have eq87845 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq86618 eq76227
    | exact resolve eq76227 eq86618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76227 eq86618
  have eq87855 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq73835 eq87845
    | exact resolve eq87845 eq73835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87845
  have eq91002 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq87855 eq75163
    | exact resolve eq75163 eq87855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75163 eq87855
  have eq91006 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq91002
  have eq91010 : x = (M.op x y) := by
    first
    | (have r₁ := eq91006
       have r₂ := eq28
       grind)
    | exact resolve eq91006 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91006
  have eq91018 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq91010 eq21
    | exact resolve eq21 eq91010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq91325 : x = (k x (M.op x x)) := by
    first
    | exact superpose eq91010 eq75122
    | exact resolve eq75122 eq91010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75122
  have eq91328 : x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq91325
       have i₂ := eq73529
       grind)
    | exact superpose eq73529 eq91325
    | exact resolve eq91325 eq73529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73529 eq91325
  have eq91487 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq91018
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq91018
    | exact resolve eq91018 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91018
  have eq91489 : x = (k x x) := by
    first
    | exact superpose eq91010 eq91328
    | exact resolve eq91328 eq91010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91010 eq91328
  have eq92019 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3458 x
       have i₂ := eq91489
       grind)
    | exact superpose eq91489 eq3458
    | (have j0 := eq3458 x
       grind)
    | exact resolve eq3458 eq91489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3458 eq91489
  have eq92023 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq92019
  have eq92033 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq92023
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq92023
    | exact resolve eq92023 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq92023
  have eq92049 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq73835 eq92033
    | exact resolve eq92033 eq73835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73835 eq92033
  have eq92064 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq91487 eq92049
    | exact resolve eq92049 eq91487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91487 eq92049
  have eq92077 : False := by grind
  exact eq92077

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyx_pxx_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
    intro X0 X1 X2
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
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
  have eq70 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq70
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq70
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq89
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq89
    | exact resolve eq89 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq95
    | exact resolve eq95 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq605 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X2 X0 X1
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq810 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq605 X1 x X3
       have i₂ := eq605 X1 x X0
       grind)
    | exact superpose eq605 eq605
    | exact resolve eq605 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq822 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 x
       have i₂ := eq605 X1 x X0
       grind)
    | exact superpose eq605 eq14
    | exact resolve eq14 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq857 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq822 X0 (M.op X0 X0)
       have i₂ := eq822 X0 X0
       grind)
    | exact superpose eq822 eq822
    | exact resolve eq822 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq964 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq857 X0
       grind)
    | exact superpose eq857 eq14
    | exact resolve eq14 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq1409 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq810 X0 (M.op X1 (M.op X1 X0)) X2
       have i₂ := eq822 X1 X0
       grind)
    | exact superpose eq822 eq810
    | exact resolve eq810 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810 eq822
  have eq23124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq23124
    | exact resolve eq23124 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23124
  have eq23136 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq23125
       have r₂ := eq28
       grind)
    | exact resolve eq23125 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23125
  have eq23150 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op X0 (M.op (σ y) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq23136 eq1409
    | exact resolve eq1409 eq23136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23136
  have eq23158 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq23150 x
       have i₂ := eq964 sF3 x
       grind)
    | exact superpose eq964 eq23150
    | exact resolve eq23150 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23150
  have eq23159 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq23158
  have eq23165 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq23159
  have eq23217 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq23165
    | exact resolve eq23165 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23165
  have eq23958 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23217 eq96
    | exact resolve eq96 eq23217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq23217
  have eq23970 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq23958
  have eq23972 : y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq23970
       have r₂ := eq28
       grind)
    | exact resolve eq23970 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23970
  have eq23986 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op X0 (M.op y y))) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1409 x y X0
       have i₂ := eq23972
       grind)
    | exact superpose eq23972 eq1409
    | exact resolve eq1409 eq23972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23972
  have eq23994 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq23986 x
       have i₂ := eq964 y x
       grind)
    | exact superpose eq964 eq23986
    | exact resolve eq23986 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23986
  have eq23995 : y = (M.op x x) := by grind
  clear eq23994
  have eq24001 : (M.op x y) = (k y x) := by grind
  clear eq23995
  have eq24053 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq24001
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24001
    | exact resolve eq24001 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq24001
  have eq24971 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq24053
       grind)
    | exact superpose eq24053 eq70
    | exact resolve eq70 eq24053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq24053
  have eq24997 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq21 eq24971
    | exact resolve eq24971 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq24971
  have eq25476 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq24997 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq24997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25477 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq25476
    | exact resolve eq25476 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25476
  have eq25488 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq25477
       have r₂ := eq28
       grind)
    | exact resolve eq25477 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25477
  have eq35210 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op X0 (M.op (σ y) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq25488 eq1409
    | exact resolve eq1409 eq25488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409 eq25488
  have eq35218 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq35210 x
       have i₂ := eq964 sF3 x
       grind)
    | exact superpose eq964 eq35210
    | exact resolve eq35210 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964 eq35210
  have eq35219 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq35218
  have eq35599 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq35219
  have eq35651 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24997 eq35599
    | exact resolve eq35599 eq24997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24997 eq35599
  have eq35658 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq35651
    | exact resolve eq35651 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq35651
  have eq35659 : False := by grind
  exact eq35659

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pxx_pyy_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq30 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
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
  have eq189 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq189 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq208 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq207 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq367 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq208 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq371 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq367 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq367 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq367 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq367 X0 X1
       have r₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact resolve eq367 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq528 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X1 X2 X1 X0
       have i₂ := eq9 X1 X1 X0
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq679 : ∀ X0 X2 : G, (M.op X2 (M.op X0 (M.op X0 X2))) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X2 X2 x
       have i₂ := eq528 x X2 X0
       grind)
    | exact superpose eq528 eq9
    | exact resolve eq9 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq719 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq679 X0 (M.op X0 X0)
       have i₂ := eq679 X0 X0
       grind)
    | exact superpose eq679 eq679
    | exact resolve eq679 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq751 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq679 (M.op X0 X0) X0
       have i₂ := eq719 X0
       grind)
    | exact superpose eq719 eq679
    | exact resolve eq679 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679 eq719
  have eq761 : ∀ X0 : G, (M.op X0 (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    grind
  clear eq751
  have eq838 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op X1 (M.op X1 (M.op X0 (k (M.op X0 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (M.op X0 X0) X0) X1 X0
       have i₂ := eq761 X0
       grind)
    | exact superpose eq761 eq9
    | exact resolve eq9 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq848 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq838 X0 X1
       have i₂ := eq761 X0
       grind)
    | exact superpose eq761 eq838
    | exact resolve eq838 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761 eq838
  have eq1392 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq848 X1 X1
       have i₂ := eq371 X0 X1
       grind)
    | (have i₁ := eq848 X0 X1
       have i₂ := eq371 (M.op X1 X0) X1
       grind)
    | exact superpose eq371 eq848
    | (have j1 := eq371 X0 X1
       grind)
    | exact resolve eq848 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371 eq848
  have eq1428 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1392 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392
  have eq1462 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1428 (σ X0) (σ X1)
       grind)
    | exact superpose eq1428 eq15
    | exact resolve eq15 eq1428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1475 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1462 X0 X1
       have i₂ := eq1428 X0 X1
       grind)
    | exact superpose eq1428 eq1462
    | exact resolve eq1462 eq1428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428 eq1462
  have eq1568 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1475 y x
       grind)
    | exact superpose eq1475 eq16
    | (have r₁ := eq16
       have r₂ := eq1475 y x
       grind)
    | exact resolve eq16 eq1475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475
  have eq1578 : False := by grind
  exact eq1578

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
    | (have r₁ := eq22 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq27 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
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
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
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
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq35 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq37 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq38 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       have j1 := eq39 X0 X1
       grind)
    | (have r₁ := eq47 X0 X1
       have r₂ := eq39 X0 X1
       grind)
    | exact resolve eq47 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq47
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq50
    | (have j0 := eq50 X0 X1
       grind)
    | exact resolve eq50 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq50
  have eq98 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq102 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq98 X0 X1
       have j1 := eq52 X1 X0
       grind)
    | (have r₁ := eq98 X1 X0
       have r₂ := eq52 X0 X1
       grind)
    | (have r₁ := eq98 X1 X1
       have r₂ := eq52 X1 X1
       grind)
    | exact resolve eq98 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq98
  have eq268 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq102 (σ X1) (σ X0)
       grind)
    | exact superpose eq102 eq15
    | exact resolve eq15 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq268 X0 X1
       have i₂ := eq102 X1 X0
       grind)
    | exact superpose eq102 eq268
    | exact resolve eq268 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq268
  have eq278 : False := by grind
  exact eq278

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxy_pxx_pyx_Equation723 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op (M.op x y) y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
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
  have eq80 : x ≠ (M.op x y) ∨ x = y ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq88 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq92 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq88
  have eq93 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq92
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq87
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq87
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq87
       grind)
    | exact superpose eq87 eq16
    | exact resolve eq16 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq94
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq94
    | exact resolve eq94 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq100
    | exact resolve eq100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq127 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq16
    | exact resolve eq16 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq670 : ∀ X0 : G, (M.op (M.op X0 (M.op (M.op x y) y)) (M.op (M.op x y) y)) = (M.op y (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq797 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq798 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq797
    | exact resolve eq797 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq801 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq798
       have r₂ := eq28
       grind)
    | exact resolve eq798 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq803 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq801
    | exact resolve eq801 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq806 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq803 eq81
    | (have r₁ := eq81
       have r₂ := eq803
       grind)
    | exact resolve eq81 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq807 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq803 eq54
    | exact resolve eq54 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq803
  have eq809 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq806
  have eq810 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq809
  have eq811 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27 eq807
    | (have j0 := eq807 X0
       grind)
    | exact resolve eq807 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq816 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq810 eq102
    | exact resolve eq102 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq817 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq810 eq99
    | exact resolve eq99 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq810
  have eq820 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq816
  have eq824 : (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq127 eq817
    | exact resolve eq817 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq817
  have eq827 : (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq824
       have r₂ := eq80
       grind)
    | exact resolve eq824 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq824
  have eq830 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq87
       have i₂ := eq827
       grind)
    | exact superpose eq827 eq87
    | exact resolve eq87 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq827
  have eq835 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq830
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq830
    | exact resolve eq830 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq843 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq835 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq844 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq843
  have eq848 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq844
    | exact resolve eq844 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq851 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq848
    | exact resolve eq848 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq1074 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq811 eq56
    | exact resolve eq56 eq811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1299 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X0 (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1074 eq14
    | exact resolve eq14 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074
  have eq2558 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq811 eq1299
    | exact resolve eq1299 eq811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811 eq1299
  have eq2574 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2558
  have eq2601 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2574 eq820
    | exact resolve eq820 eq2574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820 eq2574
  have eq2608 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2601
  have eq2610 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2608
       have r₂ := eq28
       grind)
    | exact resolve eq2608 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2608
  have eq2613 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2610 eq30
    | exact resolve eq30 eq2610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2610
  have eq2635 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq2613
    | exact resolve eq2613 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2613
  have eq2636 : x = (M.op x y) ∨ x = y := by grind
  clear eq2635
  have eq2639 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2636 eq21
    | exact resolve eq21 eq2636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2641 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2636 eq53
    | exact resolve eq53 eq2636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq2656 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op x y)) = (M.op y (M.op x y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2636 eq670
    | exact resolve eq670 eq2636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670 eq2636
  have eq2659 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op x y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2656 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2656
    | (have j0 := eq2656 X0
       grind)
    | exact resolve eq2656 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2656
  have eq2673 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2641 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2641
    | (have j0 := eq2641 X0
       grind)
    | exact resolve eq2641 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2641
  have eq2675 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq2639
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2639
    | exact resolve eq2639 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2639
  have eq3393 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 (M.op y (M.op x y)))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2659 eq14
    | exact resolve eq14 eq2659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2659
  have eq4532 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2673 eq3393
    | exact resolve eq3393 eq2673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2673 eq3393
  have eq4546 : (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq4532
  have eq4550 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq93
       have i₂ := eq4546
       grind)
    | exact superpose eq4546 eq93
    | exact resolve eq93 eq4546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq4546
  have eq4561 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq4550
    | exact resolve eq4550 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4550
  have eq4568 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq4561 eq851
    | exact resolve eq851 eq4561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851 eq4561
  have eq4578 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq4568
  have eq4584 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq4578
       have r₂ := eq28
       grind)
    | exact resolve eq4578 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4578
  have eq4586 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq4584 eq28
    | exact resolve eq28 eq4584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4584
  have eq4632 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq4586
       have r₂ := eq2675
       grind)
    | exact resolve eq4586 eq2675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2675 eq4586
  have eq4940 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq4632 eq30
    | exact resolve eq30 eq4632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq4632
  have eq4975 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq4940
    | exact resolve eq4940 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4940
  have eq4976 : x = y := by grind
  clear eq4975
  have eq4979 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq4976
       grind)
    | exact superpose eq4976 eq19
    | exact resolve eq19 eq4976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq4980 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq4976
       grind)
    | exact superpose eq4976 eq25
    | exact resolve eq25 eq4976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq4976
  have eq5009 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq4980
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq4980
    | exact resolve eq4980 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq4980
  have eq5012 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5009 eq27
    | exact resolve eq27 eq5009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq5009
  have eq5202 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5012 eq68
    | exact resolve eq68 eq5012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq5012
  have eq5218 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq5202
       have i₂ := eq4979
       grind)
    | exact superpose eq4979 eq5202
    | exact resolve eq5202 eq4979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4979 eq5202
  have eq5221 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5218 eq15
    | exact resolve eq15 eq5218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5218
  have eq5267 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq5221
    | exact resolve eq5221 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq5221
  have eq5276 : False := by grind
  exact eq5276

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_pyy_pyx_pxx_pxy_Equation731 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq31 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
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
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X1) X0) (M.op X2 X2) X2
       have i₂ := eq9 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq85 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq10
    | exact resolve eq10 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq124 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq85
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq209 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X3 (M.op X1 X1) X2
       have i₂ := eq53 (M.op X1 X1) X0 X1
       grind)
    | (have i₁ := eq53 X3 (M.op X1 X1) X2
       have i₂ := eq53 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k X1 (M.op X1 (M.op (M.op X2 X2) X0))) = (M.op (M.op X1 (M.op (M.op X2 X2) X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (M.op X1 (M.op (M.op X2 X2) X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X1 (M.op X1 (M.op (M.op X2 X2) X0))
       grind)
    | (have r₁ := eq12 X0 (M.op X0 (M.op (M.op X2 X2) X0))
       have r₂ := eq9 X0 X0 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq234 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq234 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq234 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq273 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq61
       have i₂ := eq14 sF2 sF3
       grind)
    | exact superpose eq14 eq61
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq274 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq273
    | exact resolve eq273 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq278 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq274
    | exact resolve eq274 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq282 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq124 X0 X0
       have i₂ := eq235 X0
       grind)
    | exact superpose eq235 eq124
    | exact resolve eq124 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq235 (σ X0)
       grind)
    | exact superpose eq235 eq15
    | exact resolve eq15 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq284 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq283 X0
       have i₂ := eq235 X0
       grind)
    | exact superpose eq235 eq283
    | exact resolve eq283 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq285 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq282 X0
       have i₂ := eq235 (τ X0)
       grind)
    | exact superpose eq235 eq282
    | exact resolve eq282 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235 eq282
  have eq961 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X4 (M.op X4 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq52 X1 X4 x x
       have i₂ := eq52 X1 X0 x x
       grind)
    | (have i₁ := eq52 X0 X1 x x
       have i₂ := eq52 X0 (M.op x x) x x
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq978 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X4 X4) X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq9 (M.op (M.op X4 X4) X1) X2 x
       have i₂ := eq52 X1 X0 x X4
       grind)
    | (have i₁ := eq9 (M.op (M.op X2 X2) X0) X1 X2
       have i₂ := eq52 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq979 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X2 X2) x
       have i₂ := eq52 X1 X0 X2 x
       grind)
    | (have i₁ := eq9 X0 (M.op X2 X2) X2
       have i₂ := eq52 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq984 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op X0 (M.op X0 (M.op X1 X1))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X3 (M.op (M.op X1 X1) (M.op X1 X1)) X2
       have i₂ := eq52 (M.op X1 X1) X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1028 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq961 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq961
    | (have j0 := eq961 X0 y x
       grind)
    | exact resolve eq961 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1029 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq961
    | (have j0 := eq961 X0 (σ y) (σ x)
       grind)
    | exact resolve eq961 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1077 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 y))) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq961 X0 (M.op X0 y) X1
       have i₂ := eq1028 X0
       grind)
    | (have i₁ := eq961 x (M.op x y) x
       have i₂ := eq1028 X0
       grind)
    | exact superpose eq1028 eq961
    | exact resolve eq961 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1100 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1029 eq9
    | exact resolve eq9 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1105 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 (σ y)))) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq1029 eq961
    | exact resolve eq961 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1113 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq1029 eq9
    | exact resolve eq9 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1135 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (M.op X0 (M.op X1 X1))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1100 (M.op (M.op X1 X1) (M.op X1 X1))
       have i₂ := eq52 (M.op X1 X1) X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq52 eq1100
    | exact resolve eq1100 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1157 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X3) X0)) = (M.op (M.op X1 X1) (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq979 X2 (M.op X2 (M.op (M.op X3 X3) X0)) X1
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq979
    | exact resolve eq979 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1158 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X0 X0) (M.op X1 (M.op x (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq979 X1 (M.op X1 y) X0
       have i₂ := eq1028 X1
       grind)
    | (have i₁ := eq979 x (M.op x y) x
       have i₂ := eq1028 X0
       grind)
    | exact superpose eq1028 eq979
    | exact resolve eq979 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1159 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op (M.op X0 X0) (M.op X1 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq1029 eq979
    | exact resolve eq979 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1208 : ∀ X0 X1 : G, (M.op X1 (M.op x (M.op x y))) = (M.op X1 (M.op X0 (M.op X0 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1077 X1 X1
       have i₂ := eq961 X1 y X0
       grind)
    | (have i₁ := eq1077 X1 X1
       have i₂ := eq961 X0 y X1
       grind)
    | exact superpose eq961 eq1077
    | exact resolve eq1077 eq961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1489 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (σ y))) = (M.op (M.op X1 X1) (M.op X2 (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1105 eq979
    | exact resolve eq979 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105
  have eq1610 : ∀ X0 X1 : G, (σ y) = (M.op X1 (M.op X1 (M.op X0 (M.op X0 (M.op (σ x) (M.op (σ x) (σ y))))))) := by
    intro X0 X1
    first
    | exact superpose eq1113 eq9
    | exact resolve eq9 eq1113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113
  have eq1720 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op (M.op X1 X1) X0))) = (M.op (M.op X0 (M.op (M.op X1 X1) X0)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq221 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq1755 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (M.op (M.op x (M.op x y)) y) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1158 eq9
    | exact resolve eq9 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1760 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op x (M.op x y)) y) X1) := by
    intro X0 X1
    first
    | exact superpose eq1158 eq53
    | exact resolve eq53 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1763 : ∀ X0 X1 : G, (M.op (M.op (M.op x (M.op x y)) y) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1158 eq979
    | exact resolve eq979 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158
  have eq1862 : (M.op (τ (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y))))) (τ (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))))) = (τ (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y))) := by
    first
    | exact superpose eq1159 eq285
    | exact resolve eq285 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159
  have eq1880 : (τ (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y))) = (M.op (M.op (τ (M.op (σ x) (M.op (σ x) (σ y)))) (τ (M.op (σ x) (M.op (σ x) (σ y))))) (M.op (τ (M.op (σ x) (M.op (σ x) (σ y)))) (τ (M.op (σ x) (M.op (σ x) (σ y)))))) := by
    first
    | (have i₁ := eq1862
       have i₂ := eq285 (M.op sF2 sF4)
       grind)
    | exact superpose eq285 eq1862
    | exact resolve eq1862 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1862
  have eq1889 : (τ (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y))) = (M.op (M.op (M.op x (M.op x y)) y) (M.op (τ (M.op (σ x) (M.op (σ x) (σ y)))) (τ (M.op (σ x) (M.op (σ x) (σ y)))))) := by
    first
    | (have i₁ := eq1880
       have i₂ := eq1760 (τ (M.op sF2 sF4)) (M.op (τ (M.op sF2 sF4)) (τ (M.op sF2 sF4)))
       grind)
    | exact superpose eq1760 eq1880
    | exact resolve eq1880 eq1760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1880
  have eq2059 : (σ y) = (M.op (M.op y (M.op x (M.op x y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1135 x y
       have i₂ := eq1077 y x
       grind)
    | exact superpose eq1077 eq1135
    | exact resolve eq1135 eq1077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq2087 : ∀ X0 : G, (σ y) = (M.op (M.op y (M.op x (M.op x y))) (M.op X0 (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq1029 eq2059
    | exact resolve eq2059 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029 eq2059
  have eq2853 : ∀ X0 X1 X2 : G, (σ y) = (M.op X2 (M.op (M.op X0 X0) (M.op (M.op X1 X1) (M.op X2 (M.op (σ x) (M.op (σ x) (σ y))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1610 (M.op x x) (M.op X2 X2)
       have i₂ := eq52 (M.op (M.op x x) (M.op sF2 sF4)) X1 X2 x
       grind)
    | (have i₁ := eq1610 X1 X1
       have i₂ := eq52 (M.op X1 (M.op sF2 sF4)) X1 X2 x
       grind)
    | exact superpose eq52 eq1610
    | exact resolve eq1610 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1610
  have eq2898 : ∀ X1 X2 : G, (σ y) = (M.op X2 (M.op (M.op X1 X1) (M.op X2 (σ y)))) := by
    intro X1 X2
    first
    | exact superpose eq1489 eq2853
    | exact resolve eq2853 eq1489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489 eq2853
  have eq2918 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op X0 X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq2898
    | (have j0 := eq2898 X0 (σ x)
       grind)
    | exact resolve eq2898 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2898
  have eq2964 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (M.op (M.op X0 (M.op X0 (M.op X1 X1))) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2918 (M.op (M.op X1 X1) (M.op X1 X1))
       have i₂ := eq52 (M.op X1 X1) X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq52 eq2918
    | exact resolve eq2918 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq2918
  have eq3914 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X2) X0)) = (M.op (M.op (M.op x (M.op x y)) y) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1763 X1 (M.op X1 (M.op (M.op X2 X2) X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq1763
    | exact resolve eq1763 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3915 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (M.op x (M.op x y)) y) X0)) = (M.op (M.op (M.op x (M.op x y)) y) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq1755 eq1763
    | exact resolve eq1763 eq1755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6118 : (M.op (M.op (M.op x (M.op x y)) y) (σ y)) = (M.op (M.op y (M.op x (M.op x y))) (σ y)) := by
    first
    | exact superpose eq2087 eq1755
    | exact resolve eq1755 eq2087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1755 eq2087
  have eq7532 : (σ y) = (M.op (σ x) (M.op (M.op y (M.op x (M.op x y))) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq2964 y y
       have i₂ := eq1208 y y
       grind)
    | exact superpose eq1208 eq2964
    | exact resolve eq2964 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208 eq2964
  have eq7572 : (M.op (M.op (M.op x (M.op x y)) y) (M.op (σ x) (σ y))) = (M.op (M.op y (M.op x (M.op x y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq7532 eq1763
    | exact resolve eq1763 eq7532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1763 eq7532
  have eq7577 : (M.op (σ x) (M.op (M.op (M.op x (M.op x y)) y) (σ y))) = (M.op (M.op y (M.op x (M.op x y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3915 eq7572
    | exact resolve eq7572 eq3915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7572
  have eq7581 : (M.op (σ x) (M.op (M.op y (M.op x (M.op x y))) (σ y))) = (M.op (M.op y (M.op x (M.op x y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq6118 eq7577
    | exact resolve eq7577 eq6118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6118 eq7577
  have eq8388 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op y (M.op x (M.op x y))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq209 y (M.op y y) X0 X1
       have i₂ := eq1077 y (M.op y y)
       grind)
    | exact superpose eq1077 eq209
    | exact resolve eq209 eq1077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq1077
  have eq9433 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op (M.op y (M.op x (M.op x y))) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq8388 x X0
       grind)
    | exact superpose eq8388 eq9
    | exact resolve eq9 eq8388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9438 : ∀ X0 : G, (M.op (M.op (M.op x (M.op x y)) y) X0) = (M.op (M.op y (M.op x (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq1760 x X0
       have i₂ := eq8388 x X0
       grind)
    | exact superpose eq8388 eq1760
    | exact resolve eq1760 eq8388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1760
  have eq10118 : ∀ X0 X1 : G, (M.op (M.op (M.op x (M.op x y)) y) (M.op X1 X0)) = (M.op X1 (M.op (M.op y (M.op x (M.op x y))) X0)) := by
    intro X0 X1
    first
    | exact superpose eq9438 eq3915
    | exact resolve eq3915 eq9438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3915
  have eq10143 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X2) X0)) = (M.op (M.op y (M.op x (M.op x y))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq9438 eq3914
    | exact resolve eq3914 eq9438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3914
  have eq10226 : (τ (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y))) = (M.op (M.op y (M.op x (M.op x y))) (M.op (τ (M.op (σ x) (M.op (σ x) (σ y)))) (τ (M.op (σ x) (M.op (σ x) (σ y)))))) := by
    first
    | exact superpose eq9438 eq1889
    | exact resolve eq1889 eq9438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1889
  have eq10577 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op y (M.op x (M.op x y))) X0)) = (M.op (M.op y (M.op x (M.op x y))) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq9438 eq10118
    | exact resolve eq10118 eq9438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9438 eq10118
  have eq14362 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq978 X1 X2 X1 X3
       have i₂ := eq961 X1 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq978 X1 X2 X1 X3
       have i₂ := eq961 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq961 eq978
    | exact resolve eq978 eq961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978
  have eq15728 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op X1 (M.op X0 (M.op X0 X1))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq984 X1 X1 X2 X3
       have i₂ := eq961 X1 X1 X0
       grind)
    | (have i₁ := eq984 X1 X1 X2 X3
       have i₂ := eq961 X0 X1 X1
       grind)
    | exact superpose eq961 eq984
    | exact resolve eq984 eq961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961 eq984
  have eq27802 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X0 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq979 X0 X2 x
       have i₂ := eq1157 (M.op X0 X2) x X0 X1
       grind)
    | (have i₁ := eq979 (M.op x x) X1 X2
       have i₂ := eq1157 (M.op (M.op x x) X1) X1 (M.op X2 X2) x
       grind)
    | exact superpose eq1157 eq979
    | exact resolve eq979 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979
  have eq28015 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op x (M.op x y))) X2) = (M.op (M.op X0 (M.op (M.op X1 X1) X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8388 (M.op X0 X0) X2
       have i₂ := eq1157 X0 X0 X0 X1
       grind)
    | (have i₁ := eq8388 (M.op (M.op x x) X0) X1
       have i₂ := eq1157 X0 X1 (M.op (M.op x x) X0) x
       grind)
    | exact superpose eq1157 eq8388
    | exact resolve eq8388 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157
  have eq28038 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op (M.op X1 X1) X0))) = (M.op (M.op y (M.op x (M.op x y))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1720 X0 X1
       have i₂ := eq28015 X0 X1 X0
       grind)
    | exact superpose eq28015 eq1720
    | exact resolve eq1720 eq28015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1720 eq28015
  have eq28740 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op x (M.op x y))) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27802 X0 x X1
       have i₂ := eq8388 x (M.op X0 X1)
       grind)
    | exact superpose eq8388 eq27802
    | exact resolve eq27802 eq8388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8388
  have eq32051 : (M.op (M.op y (M.op x (M.op x y))) (M.op (σ x) (M.op (σ x) (σ y)))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y))) := by
    first
    | exact superpose eq1100 eq28038
    | exact resolve eq28038 eq1100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100
  have eq32088 : ∀ X0 X1 X2 X3 : G, (M.op (M.op y (M.op x (M.op x y))) (M.op X2 (M.op X2 (M.op (M.op X3 X3) X1)))) = (k (M.op X2 (M.op X2 (M.op (M.op X3 X3) X1))) (M.op (M.op X2 (M.op X2 (M.op (M.op X3 X3) X1))) (M.op (M.op X0 X0) X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq28038 (M.op X2 (M.op X2 (M.op (M.op X3 X3) X1))) X3
       have i₂ := eq14362 X2 (M.op X3 X3) X1 X0
       grind)
    | exact superpose eq14362 eq28038
    | exact resolve eq28038 eq14362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14362 eq28038
  have eq32188 : ∀ X1 X2 X3 : G, (M.op (M.op y (M.op x (M.op x y))) (M.op X2 (M.op X2 (M.op (M.op X3 X3) X1)))) = (k (M.op X2 (M.op X2 (M.op (M.op X3 X3) X1))) (M.op (M.op y (M.op x (M.op x y))) (M.op (M.op X2 (M.op X2 (M.op (M.op X3 X3) X1))) X1))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq32088 x X1 X2 X3
       have i₂ := eq10143 X1 (M.op X2 (M.op X2 (M.op (M.op X3 X3) X1))) x
       grind)
    | exact superpose eq10143 eq32088
    | exact resolve eq32088 eq10143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10143 eq32088
  have eq32212 : (M.op (σ x) (M.op (M.op y (M.op x (M.op x y))) (M.op (σ x) (σ y)))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y))) := by
    first
    | exact superpose eq10577 eq32051
    | exact resolve eq32051 eq10577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10577 eq32051
  have eq32267 : ∀ X1 : G, (M.op (M.op y (M.op x (M.op x y))) X1) = (k X1 (M.op (M.op y (M.op x (M.op x y))) (M.op X1 X1))) := by
    intro X1
    by_contra hcon
    push Not at hcon
    have f32267_12 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op x (M.op x y))) (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0)))) = (k (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) (M.op (M.op y (M.op x (M.op x y))) (M.op (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) X0))) := by
      intro X0 X1 X2
      grind
    have f32267_14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
      intro X0 X1 X2
      grind
    have f32267_22 : (M.op (M.op y (M.op x (M.op x y))) X1) ≠ (k X1 (M.op (M.op y (M.op x (M.op x y))) (M.op X1 X1))) := by grind
    have f32267_23 : ∀ X0 : G, (M.op (M.op y (M.op x (M.op x y))) X0) = (k X0 (M.op (M.op y (M.op x (M.op x y))) (M.op X0 X0))) := by
      intro X0
      first
      | (have i₁ := f32267_12 X0 x x
         have i₂ := f32267_14 X0 x x
         grind)
      | exact superpose f32267_14 f32267_12
      | exact resolve f32267_12 f32267_14
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f32267_126 : (M.op (M.op y (M.op x (M.op x y))) X1) ≠ (M.op (M.op y (M.op x (M.op x y))) X1) := by
      first
      | (have i₁ := f32267_22
         have i₂ := f32267_23 X1
         grind)
      | exact superpose f32267_23 f32267_22
      | (have r₁ := f32267_22
         have r₂ := f32267_23 X1
         grind)
      | exact resolve f32267_22 f32267_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f32267_127 : False := by grind
    exact f32267_127
  clear eq32188
  have eq32282 : (M.op (σ x) (M.op (σ x) (M.op (M.op y (M.op x (M.op x y))) (σ y)))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y))) := by
    first
    | exact superpose eq7581 eq32212
    | exact resolve eq32212 eq7581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7581 eq32212
  have eq32307 : (σ y) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y))) := by
    first
    | exact superpose eq9433 eq32282
    | exact resolve eq32282 eq9433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9433 eq32282
  have eq32333 : (τ (σ y)) = (k (τ (M.op (σ x) (M.op (σ x) (σ y)))) (τ (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)))) := by
    first
    | exact superpose eq32307 eq124
    | exact resolve eq124 eq32307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq32307
  have eq32334 : (τ (σ y)) = (k (τ (M.op (σ x) (M.op (σ x) (σ y)))) (M.op (M.op y (M.op x (M.op x y))) (M.op (τ (M.op (σ x) (M.op (σ x) (σ y)))) (τ (M.op (σ x) (M.op (σ x) (σ y))))))) := by
    first
    | exact superpose eq10226 eq32333
    | exact resolve eq32333 eq10226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10226 eq32333
  have eq32336 : (τ (σ y)) = (M.op (M.op y (M.op x (M.op x y))) (τ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq32267 eq32334
    | exact resolve eq32334 eq32267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32267 eq32334
  have eq32338 : y = (M.op (M.op y (M.op x (M.op x y))) (τ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq39 eq32336
    | exact resolve eq32336 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32336
  have eq32391 : (τ (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op y (M.op x (M.op x y))) (M.op (M.op y (M.op x (M.op x y))) y)) := by
    first
    | exact superpose eq32338 eq28740
    | exact resolve eq28740 eq32338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28740 eq32338
  have eq32392 : (M.op x (M.op x y)) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq32391
       have i₂ := eq1028 (M.op y (M.op x sF0))
       grind)
    | exact superpose eq1028 eq32391
    | exact resolve eq32391 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028 eq32391
  have eq32444 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq32392 eq11
    | exact resolve eq11 eq32392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34597 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 (M.op X1 (M.op X1 X0))) (M.op X2 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq27802 X2 x X3
       have i₂ := eq15728 X1 X0 x (M.op X2 X3)
       grind)
    | exact superpose eq15728 eq27802
    | exact resolve eq27802 eq15728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15728 eq27802
  have eq117141 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq278
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq278
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq278 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq117194 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq117141
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117141
    | exact resolve eq117141 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117141
  have eq117198 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq117194
    | exact resolve eq117194 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117194
  have eq117200 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq117198
       have r₂ := eq27
       grind)
    | exact resolve eq117198 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117198
  have eq117201 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq117200
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117200
    | exact resolve eq117200 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117200
  have eq117404 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (M.op X0 (M.op X1 (M.op X1 X0))) (M.op (σ y) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op y x) = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq117201 eq34597
    | exact resolve eq34597 eq117201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117201
  have eq117406 : (M.op y x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq117404 x x
       have i₂ := eq34597 x x sF3 sF2
       grind)
    | exact superpose eq34597 eq117404
    | exact resolve eq117404 eq34597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117404
  have eq117640 : ∀ X0 X1 : G, y = (M.op y (M.op (M.op X0 (M.op X1 (M.op X1 X0))) (M.op y x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq34597 X0 X1 y y
       have i₂ := eq117406
       grind)
    | exact superpose eq117406 eq34597
    | exact resolve eq34597 eq117406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117406
  have eq117642 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq117640 x x
       have i₂ := eq34597 x x y x
       grind)
    | exact superpose eq34597 eq117640
    | exact resolve eq117640 eq34597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117640
  have eq117716 : (M.op x (M.op x y)) = (τ (M.op (σ x) (σ x))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq117642 eq32392
    | exact resolve eq32392 eq117642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32392 eq117642
  have eq117749 : (M.op x (M.op x y)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq117716
       have i₂ := eq285 sF2
       grind)
    | exact superpose eq285 eq117716
    | exact resolve eq117716 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285 eq117716
  have eq117759 : (M.op x x) = (M.op x (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq38 eq117749
    | exact resolve eq117749 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117749
  have eq120808 : ∀ X0 X1 : G, (M.op x y) = (M.op x (M.op (M.op X0 (M.op X1 (M.op X1 X0))) (M.op x x))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq117759 eq34597
    | exact resolve eq34597 eq117759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117759
  have eq120810 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq120808 x x
       have i₂ := eq34597 x x x x
       grind)
    | exact superpose eq34597 eq120808
    | exact resolve eq120808 eq34597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120808
  have eq120811 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq120810
  have eq120841 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq120811 eq39
    | exact resolve eq39 eq120811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq120811
  have eq120949 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq120841
    | exact resolve eq120841 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq120841
  have eq120950 : x = (M.op x y) ∨ x = y := by grind
  clear eq120949
  have eq120956 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq120950 eq20
    | exact resolve eq20 eq120950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121032 : (σ (M.op x x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq120950 eq32444
    | exact resolve eq32444 eq120950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32444 eq120950
  have eq121063 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq121032
       have i₂ := eq284 x
       grind)
    | exact superpose eq284 eq121032
    | exact resolve eq121032 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121032
  have eq121066 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq120956
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq120956
    | exact resolve eq120956 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120956
  have eq121067 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq121063
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq121063
    | exact resolve eq121063 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121063
  have eq121461 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op X0 (M.op X1 (M.op X1 X0))) (M.op (σ x) (σ x)))) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq121067 eq34597
    | exact resolve eq34597 eq121067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121067
  have eq121464 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq121461 x x
       have i₂ := eq34597 x x sF2 sF2
       grind)
    | exact superpose eq34597 eq121461
    | exact resolve eq121461 eq34597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34597 eq121461
  have eq121502 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq121464 eq27
    | exact resolve eq27 eq121464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121464
  have eq121595 : x = y := by
    first
    | (have r₁ := eq121502
       have r₂ := eq121066
       grind)
    | exact resolve eq121502 eq121066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121066 eq121502
  have eq121600 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq121595
       grind)
    | exact superpose eq121595 eq18
    | exact resolve eq18 eq121595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq121601 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq121595
       grind)
    | exact superpose eq121595 eq24
    | exact resolve eq24 eq121595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq121595
  have eq128138 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq121601
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq121601
    | exact resolve eq121601 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121601
  have eq129109 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq128138 eq26
    | exact resolve eq26 eq128138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq128138
  have eq135192 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq284 x
       have i₂ := eq121600
       grind)
    | exact superpose eq121600 eq284
    | exact resolve eq284 eq121600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284 eq121600
  have eq137055 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq135192
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq135192
    | exact resolve eq135192 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq135192
  have eq139952 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq129109 eq137055
    | exact resolve eq137055 eq129109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129109 eq137055
  have eq142215 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq139952
    | exact resolve eq139952 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq139952
  have eq143668 : False := by grind
  exact eq143668

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pyx_pxy_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq34 (σ X0)
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq36
    | exact resolve eq36 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq36
  have eq77 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X1
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq83
    | (have j0 := eq83 X0 X1
       grind)
    | exact resolve eq83 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq83
  have eq575 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq89 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq89 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq89 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq89 X0 X1
       grind)
    | exact resolve eq13 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq593 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq575 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq598 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq593 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq593 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq593 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq593 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq609 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq598 X0 X1
       have j1 := eq77 X0 (σ X1)
       grind)
    | (have r₁ := eq598 X0 X1
       have r₂ := eq77 X0 (σ X1)
       grind)
    | exact resolve eq598 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq598
  have eq617 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq609 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq609
    | (have j0 := eq609 X0 X1
       grind)
    | exact resolve eq609 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq618 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq617 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq624 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq618 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq618
    | exact resolve eq618 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq636 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq618 x y
       grind)
    | exact superpose eq618 eq16
    | exact resolve eq16 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq736 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq624 X0 (τ X1)
       grind)
    | exact superpose eq624 eq17
    | exact resolve eq17 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq624
  have eq754 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq736 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq736
    | exact resolve eq736 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq763 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq754 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq754
    | exact resolve eq754 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq782 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq636
       have i₂ := eq763 x y
       grind)
    | exact superpose eq763 eq636
    | exact resolve eq636 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636 eq763
  have eq783 : False := by grind
  exact eq783
