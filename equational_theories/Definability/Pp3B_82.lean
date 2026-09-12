import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_pxy_pyx_Equation723 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq101 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
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
  have eq104 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
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
  have eq417 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq440 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq417 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq417
    | (have j0 := eq417 X0 X1
       grind)
    | exact resolve eq417 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq589 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq103 X0 X2 X0 X1
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq103
    | exact resolve eq103 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq610 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq589 X1 x X3
       have i₂ := eq589 X1 x X0
       grind)
    | exact superpose eq589 eq589
    | exact resolve eq589 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq622 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 x
       have i₂ := eq589 X1 x X0
       grind)
    | exact superpose eq589 eq9
    | exact resolve eq9 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq634 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq104 X0 (M.op X2 X0) X2
       have i₂ := eq589 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq589 eq104
    | exact resolve eq104 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq646 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq634 X0 X1 X2
       have i₂ := eq104 X0 X0 X1
       grind)
    | exact superpose eq104 eq634
    | exact resolve eq634 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq667 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq622 X0 (M.op X0 X0)
       have i₂ := eq622 X0 X0
       grind)
    | exact superpose eq622 eq622
    | exact resolve eq622 eq622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq104 (M.op X0 (M.op X0 X1)) X1 X1
       have i₂ := eq622 X0 X1
       grind)
    | exact superpose eq622 eq104
    | exact resolve eq104 eq622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq677 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq674 X1 X0 X2
       have i₂ := eq622 X0 X1
       grind)
    | exact superpose eq622 eq674
    | exact resolve eq674 eq622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq681 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq667 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq667
    | exact resolve eq667 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq686 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq667 X0
       grind)
    | exact superpose eq667 eq9
    | exact resolve eq9 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq733 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq610 X0 (M.op X1 (M.op X1 X0)) X2
       have i₂ := eq622 X1 X0
       grind)
    | exact superpose eq622 eq610
    | exact resolve eq610 eq622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq735 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X2 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq610 X2 (M.op X2 X1) X3
       have i₂ := eq610 X2 X1 X0
       grind)
    | (have i₁ := eq610 X2 (M.op X2 X1) X3
       have i₂ := eq610 X0 X1 X2
       grind)
    | exact superpose eq610 eq610
    | exact resolve eq610 eq610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq799 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (M.op X1 X1)) (M.op X0 (M.op X0 (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq101 X1 (σ (M.op X1 X1))
       have i₂ := eq610 (σ (M.op X1 X1)) (σ X1) X0
       grind)
    | (have i₁ := eq101 X1 (σ (M.op X1 X1))
       have i₂ := eq610 X0 (σ X1) (σ (M.op X1 X1))
       grind)
    | exact superpose eq610 eq101
    | exact resolve eq101 eq610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq861 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq646 X0 X1 X0
       have i₂ := eq667 X0
       grind)
    | exact superpose eq667 eq646
    | exact resolve eq646 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646 eq667
  have eq936 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq103 X0 X1 X2 X1
       have i₂ := eq861 X0 X1
       grind)
    | exact superpose eq861 eq103
    | exact resolve eq103 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq937 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0 X1 X1
       have i₂ := eq861 X0 X1
       grind)
    | exact superpose eq861 eq104
    | exact resolve eq104 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq861
  have eq968 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq937 X1 X1
       have i₂ := eq610 X1 X1 X0
       grind)
    | (have i₁ := eq937 X1 X1
       have i₂ := eq610 X0 X1 X1
       grind)
    | exact superpose eq610 eq937
    | exact resolve eq937 eq610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq1064 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq936 (M.op X0 X0) (M.op X0 X0) X0
       have i₂ := eq936 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq936 eq936
    | exact resolve eq936 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1091 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1064 X0
       have i₂ := eq686 X0 (M.op X0 X0)
       grind)
    | exact superpose eq686 eq1064
    | exact resolve eq1064 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq1104 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq936 X0 X1 (M.op X0 X0)
       have i₂ := eq1091 X0
       grind)
    | exact superpose eq1091 eq936
    | exact resolve eq936 eq1091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936 eq1091
  have eq1150 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq622 (M.op X1 (M.op X1 X0)) X0
       have i₂ := eq968 X1 X0
       grind)
    | exact superpose eq968 eq622
    | exact resolve eq622 eq968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968
  have eq1374 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) = (M.op (M.op X1 X1) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1104 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq1104 X0 X1
       grind)
    | exact superpose eq1104 eq1104
    | exact resolve eq1104 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq1449 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1374 X0 X1
       have i₂ := eq677 X1 X0 X1
       grind)
    | exact superpose eq677 eq1374
    | exact resolve eq1374 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677 eq1374
  have eq1507 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq733 (M.op X1 X0) X1 X1
       have i₂ := eq733 X0 X1 X1
       grind)
    | exact superpose eq733 eq733
    | exact resolve eq733 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1510 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq733 X2 X1 X1
       have i₂ := eq610 X1 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq733 X2 X1 X1
       have i₂ := eq610 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq610 eq733
    | exact resolve eq733 eq610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1643 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X1 (M.op X2 (M.op X2 X3)))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1449 X2 X3
       have i₂ := eq733 (M.op X2 (M.op X2 X3)) X1 X0
       grind)
    | exact superpose eq733 eq1449
    | exact resolve eq1449 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733 eq1449
  have eq2179 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq440 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq440
    | (have j0 := eq440 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | exact resolve eq440 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq2594 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X2 X0))) = (M.op (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0)) (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1510 X2 X0 (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0))
       have i₂ := eq1150 X0 X1
       grind)
    | exact superpose eq1150 eq1510
    | exact resolve eq1510 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150
  have eq2758 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X2 X0))) = (M.op (M.op X1 (M.op X1 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2594 X0 X1 X2
       have i₂ := eq1507 (M.op X0 X0) (M.op X1 (M.op X1 X0))
       grind)
    | exact superpose eq1507 eq2594
    | exact resolve eq2594 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2594
  have eq2798 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X2 X0))) = (M.op (M.op X1 (M.op X1 X0)) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2758 X0 X1 X2
       have i₂ := eq1507 X0 X0
       grind)
    | exact superpose eq1507 eq2758
    | exact resolve eq2758 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1507 eq2758
  have eq2830 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2798 X0 X1 x
       have i₂ := eq622 x X0
       grind)
    | exact superpose eq622 eq2798
    | exact resolve eq2798 eq622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622 eq2798
  have eq3659 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X2 X1)) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2830 X1 X2
       have i₂ := eq610 X1 X1 X0
       grind)
    | (have i₁ := eq2830 X1 X2
       have i₂ := eq610 X0 X1 X1
       grind)
    | exact superpose eq610 eq2830
    | exact resolve eq2830 eq610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610 eq2830
  have eq30098 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X1 (M.op X1 (M.op X2 (M.op (σ (M.op X0 X0)) (σ X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq735 (σ (M.op X0 X0)) (M.op (σ (M.op X0 X0)) (σ X0)) X2 X1
       have i₂ := eq799 (σ (M.op X0 X0)) X0
       grind)
    | exact superpose eq799 eq735
    | exact resolve eq735 eq799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799
  have eq30403 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X3 X2)) (M.op X3 (M.op X3 X2))) = (M.op X1 (M.op X4 (M.op X4 (M.op X0 (M.op X0 (M.op X1 X2)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1510 X4 X1 (M.op X3 (M.op X3 X2))
       have i₂ := eq735 X3 X2 X1 X0
       grind)
    | (have i₁ := eq1510 X0 X3 (M.op X3 (M.op X2 X1))
       have i₂ := eq735 X0 X1 X2 X3
       grind)
    | exact superpose eq735 eq1510
    | exact resolve eq1510 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735 eq1510
  have eq30505 : ∀ X0 X1 X2 X4 : G, (M.op X1 (M.op X4 (M.op X4 (M.op X0 (M.op X0 (M.op X1 X2)))))) = X2 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq30403 X0 X1 X2 x X4
       have i₂ := eq3659 x X2 x
       grind)
    | exact superpose eq3659 eq30403
    | exact resolve eq30403 eq3659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3659 eq30403
  have eq30632 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X1 (M.op X1 (M.op X2 (σ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30098 X0 X1 X2
       have i₂ := eq681 X0
       grind)
    | exact superpose eq681 eq30098
    | exact resolve eq30098 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681 eq30098
  have eq66271 : ∀ X0 X1 X2 X3 : G, (σ X3) = (M.op X1 (M.op X1 (M.op X2 (M.op X2 (M.op (σ X0) (σ (M.op X0 X0))))))) ∨ (σ (M.op X3 X0)) = (M.op (σ X3) (σ X0)) ∨ (σ X0) = (σ X3) ∨ (M.op X0 X0) = (M.op X0 X3) ∨ X0 = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1643 X1 X2 (σ X0) (σ X3)
       have i₂ := eq2179 X3 X0
       grind)
    | exact superpose eq2179 eq1643
    | (have j1 := eq2179 X3 X0
       grind)
    | exact resolve eq1643 eq2179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1643 eq2179
  have eq66374 : ∀ X0 X1 X3 : G, (σ X3) = (M.op X1 (M.op X1 (M.op (σ X0) (σ X0)))) ∨ (σ (M.op X3 X0)) = (M.op (σ X3) (σ X0)) ∨ (σ X0) = (σ X3) ∨ (M.op X0 X0) = (M.op X0 X3) ∨ X0 = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq66271 X0 X1 x X3
       have i₂ := eq30632 X0 x (σ X0)
       grind)
    | exact superpose eq30632 eq66271
    | (have j0 := eq66271 X0 X1 x X3
       grind)
    | exact resolve eq66271 eq30632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30632 eq66271
  have eq66491 : ∀ X0 X3 : G, (σ X0) = (σ X3) ∨ (σ (M.op X3 X0)) = (M.op (σ X3) (σ X0)) ∨ (σ X0) = (σ X3) ∨ (M.op X0 X0) = (M.op X0 X3) ∨ X0 = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq66374 X0 x X3
       have i₂ := eq686 (σ X0) x
       grind)
    | exact superpose eq686 eq66374
    | (have j0 := eq66374 X0 x X3
       grind)
    | exact resolve eq66374 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686 eq66374
  have eq66492 : ∀ X0 X3 : G, (σ X0) = (σ X3) ∨ (σ (M.op X3 X0)) = (M.op (σ X3) (σ X0)) ∨ (M.op X0 X0) = (M.op X0 X3) ∨ X0 = X3 := by
    intro X0 X3
    first
    | (have j0 := eq66491 X0 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66491
  have eq66589 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq66492 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66492
  have eq321247 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq66589 y x
       grind)
    | exact superpose eq66589 eq16
    | (have j1 := eq66589 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq66589 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq66589 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq66589 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq66589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66589
  have eq321497 : (M.op y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq321247
  have eq322075 : ∀ X0 X1 : G, y = (M.op y (M.op X0 (M.op X0 (M.op X1 (M.op X1 (M.op y x)))))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq30505 X1 y y X0
       have i₂ := eq321497
       grind)
    | exact superpose eq321497 eq30505
    | exact resolve eq30505 eq321497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321497
  have eq322192 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq322075 x x
       have i₂ := eq30505 x y x x
       grind)
    | exact superpose eq30505 eq322075
    | exact resolve eq322075 eq30505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30505 eq322075
  have eq322193 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq322192
  have eq322275 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq322193
  have eq322362 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq322275
       grind)
    | exact superpose eq322275 eq10
    | exact resolve eq10 eq322275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322275
  have eq322564 : x = y ∨ x = y := by
    first
    | (have i₁ := eq322362
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq322362
    | exact resolve eq322362 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322362
  have eq322565 : x = y := by grind
  clear eq322564
  have eq322574 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq322565
       grind)
    | exact superpose eq322565 eq16
    | exact resolve eq16 eq322565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322565
  have eq322575 : False := by grind
  exact eq322575

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxy_pxx_pyx_Equation723 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
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
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq52 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq49
  have eq53 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq52
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
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
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
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
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq53
       grind)
    | exact superpose eq53 eq16
    | exact resolve eq16 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq92 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq88
  have eq93 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq92
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y := by
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
  clear eq87
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq94
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq94
    | exact resolve eq94 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq22 eq100
    | exact resolve eq100 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq532 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op (M.op X2 X0) X0)) = (M.op X0 (M.op (M.op X2 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq14 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X0 X2 X0 X1
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq975 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 x
       have i₂ := eq652 X1 x X0
       grind)
    | exact superpose eq652 eq14
    | exact resolve eq14 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq985 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X0 (M.op X2 X0) X2
       have i₂ := eq652 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq652 eq57
    | exact resolve eq57 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq991 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq985 X0 X1 X2
       have i₂ := eq57 X0 X0 X1
       grind)
    | exact superpose eq57 eq985
    | exact resolve eq985 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq985
  have eq1016 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq975 X0 (M.op X0 X0)
       have i₂ := eq975 X0 X0
       grind)
    | exact superpose eq975 eq975
    | exact resolve eq975 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975
  have eq1858 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq991 X0 X1 X0
       have i₂ := eq1016 X0
       grind)
    | exact superpose eq1016 eq991
    | exact resolve eq991 eq1016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991 eq1016
  have eq5937 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq532 X0 X1 X1
       have i₂ := eq1858 X0 X1
       grind)
    | exact superpose eq1858 eq532
    | exact resolve eq532 eq1858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq5938 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5937 X0 x
       have i₂ := eq1858 (M.op X0 X0) x
       grind)
    | exact superpose eq1858 eq5937
    | exact resolve eq5937 eq1858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1858 eq5937
  have eq17323 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq17324 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq28 eq17323
    | exact resolve eq17323 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17323
  have eq17335 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq17324
       have r₂ := eq29
       grind)
    | exact resolve eq17324 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17324
  have eq17341 : (τ (σ y)) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq17335 eq69
    | exact resolve eq69 eq17335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17335
  have eq17428 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq31 eq17341
    | exact resolve eq17341 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17341
  have eq17429 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq17428
  have eq17436 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq53
       have i₂ := eq17429
       grind)
    | exact superpose eq17429 eq53
    | exact resolve eq53 eq17429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq17469 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5938 x
       have i₂ := eq17429
       grind)
    | exact superpose eq17429 eq5938
    | exact resolve eq5938 eq17429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17429
  have eq17513 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq17469
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq17469
    | exact resolve eq17469 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17469
  have eq17529 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq17436
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq17436
    | exact resolve eq17436 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17436
  have eq17874 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq93
       have i₂ := eq17513
       grind)
    | exact superpose eq17513 eq93
    | exact resolve eq93 eq17513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq17513
  have eq17963 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22 eq17874
    | exact resolve eq17874 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17874
  have eq18015 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq17529 eq5938
    | exact resolve eq5938 eq17529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5938 eq17529
  have eq18059 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28 eq18015
    | exact resolve eq18015 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18015
  have eq18952 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq18059 eq17963
    | exact resolve eq17963 eq18059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17963 eq18059
  have eq19005 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18952
  have eq19015 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq19005
       have r₂ := eq29
       grind)
    | exact resolve eq19005 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19005
  have eq19019 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq19015 eq31
    | exact resolve eq31 eq19015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq19015
  have eq19158 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq19019
    | exact resolve eq19019 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq19019
  have eq19159 : x = y := by grind
  clear eq19158
  have eq19178 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq19159
       grind)
    | exact superpose eq19159 eq20
    | exact resolve eq20 eq19159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq19179 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq19159
       grind)
    | exact superpose eq19159 eq26
    | exact resolve eq26 eq19159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq19159
  have eq19305 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq19179
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19179
    | exact resolve eq19179 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq19179
  have eq19321 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq19305 eq28
    | exact resolve eq28 eq19305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq19305
  have eq19598 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq19321 eq69
    | exact resolve eq69 eq19321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq19321
  have eq19664 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq19598
       have i₂ := eq19178
       grind)
    | exact superpose eq19178 eq19598
    | exact resolve eq19598 eq19178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19178 eq19598
  have eq19676 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19664 eq15
    | exact resolve eq15 eq19664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19664
  have eq19722 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22 eq19676
    | exact resolve eq19676 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq19676
  have eq19731 : False := by grind
  exact eq19731

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxy_x_pxy_pxx_pxy_Equation731 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
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
  clear eq35
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
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq14 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X1 X1) X0) (M.op X2 X2) X2
       have i₂ := eq14 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq61 (σ X0)
       grind)
    | exact superpose eq61 eq10
    | exact resolve eq10 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq61 x
       grind)
    | exact superpose eq61 eq43
    | exact resolve eq43 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq65 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq61 sF2
       grind)
    | exact superpose eq61 eq49
    | exact resolve eq49 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq66 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq65
       have i₂ := eq61 x
       grind)
    | exact superpose eq61 eq65
    | exact resolve eq65 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq67 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq64
       have i₂ := eq61 sF2
       grind)
    | exact superpose eq61 eq64
    | exact resolve eq64 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq68 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq61 X0
       grind)
    | exact superpose eq61 eq63
    | exact resolve eq63 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq72 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq72 x y
       grind)
    | exact superpose eq72 eq44
    | (have j1 := eq72 x y
       grind)
    | exact resolve eq44 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq83
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq83
    | exact resolve eq83 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq90
    | exact resolve eq90 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq97 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq94 eq72
    | (have j0 := eq72 (σ x) (σ y)
       grind)
    | exact resolve eq72 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq97
    | exact resolve eq97 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq101 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq98
       have r₂ := eq27
       grind)
    | exact resolve eq98 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq103 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq101
    | exact resolve eq101 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq107 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq123 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq119
       have i₂ := eq61 sF3
       grind)
    | exact superpose eq61 eq119
    | exact resolve eq119 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq125 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq123
       have i₂ := eq61 y
       grind)
    | exact superpose eq61 eq123
    | exact resolve eq123 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq134 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq137 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq134
       have i₂ := eq61 sF1
       grind)
    | exact superpose eq61 eq134
    | exact resolve eq134 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq139 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq137
       have i₂ := eq61 sF0
       grind)
    | exact superpose eq61 eq137
    | exact resolve eq137 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq160 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq125
       grind)
    | exact superpose eq125 eq16
    | exact resolve eq16 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq194 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq139 eq16
    | exact resolve eq16 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq61 (τ X0)
       grind)
    | exact superpose eq61 eq34
    | exact resolve eq34 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq272 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq261 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq261
    | exact resolve eq261 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq274 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq272 X0
       have i₂ := eq61 X0
       grind)
    | exact superpose eq61 eq272
    | exact resolve eq272 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq272
  have eq372 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 X2 X3 (M.op X1 X1)
       have i₂ := eq51 (M.op X1 X1) X0 X1
       grind)
    | (have i₁ := eq51 X2 X3 (M.op X1 X1)
       have i₂ := eq51 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op (M.op X1 X1) (M.op (M.op X2 X2) X0))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 (M.op (M.op X1 X1) (M.op (M.op X2 X2) X0)) X3 X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq454 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X4 (M.op X4 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq50 X1 X4 x x
       have i₂ := eq50 X1 X0 x x
       grind)
    | (have i₁ := eq50 X0 X1 x x
       have i₂ := eq50 X0 (M.op x x) x x
       grind)
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq471 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X4 X4) X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq14 (M.op (M.op X4 X4) X1) X2 x
       have i₂ := eq50 X1 X0 x X4
       grind)
    | (have i₁ := eq14 (M.op (M.op X2 X2) X0) X1 X2
       have i₂ := eq50 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X2 X2) x
       have i₂ := eq50 X1 X0 X2 x
       grind)
    | (have i₁ := eq14 X0 (M.op X2 X2) X2
       have i₂ := eq50 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq603 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq103 eq107
    | (have r₁ := eq107
       have r₂ := eq103
       grind)
    | exact resolve eq107 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq604 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq603
  have eq609 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq604 eq94
    | exact resolve eq94 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq612 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq609
  have eq620 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq612 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq623 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq72 (σ x) (σ y)
       grind)
    | (have r₁ := eq620
       have r₂ := eq72 (σ x) (σ y)
       grind)
    | exact resolve eq620 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq620
  have eq626 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq623
    | exact resolve eq623 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq712 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq626 eq94
    | exact resolve eq94 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq626
  have eq715 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq712
  have eq719 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq715
       have r₂ := eq27
       grind)
    | exact resolve eq715 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq721 : (τ (σ (M.op x y))) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq719 eq66
    | exact resolve eq66 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq724 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ (M.op x y)) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq719 eq51
    | exact resolve eq51 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq733 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq721
    | exact resolve eq721 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq721
  have eq739 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (M.op x y) X1))) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 x
       have i₂ := eq733
       grind)
    | exact superpose eq733 eq14
    | exact resolve eq14 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq753 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq724 x X0
       have i₂ := eq733
       grind)
    | exact superpose eq733 eq724
    | exact resolve eq724 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq776 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq753 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq1284 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (M.op X0 (M.op X0 X1))) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq719 eq472
    | exact resolve eq472 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1374 : x = (M.op (σ (M.op x y)) (M.op x (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1284 x x
       have i₂ := eq733
       grind)
    | exact superpose eq733 eq1284
    | exact resolve eq1284 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq1381 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1284
    | (have j0 := eq1284 (σ x) (σ y)
       grind)
    | exact resolve eq1284 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284
  have eq1436 : x = (M.op (σ (M.op x y)) (M.op x (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq1374
  have eq1504 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq103 eq1381
    | exact resolve eq1381 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq1381
  have eq1521 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq1504
  have eq1528 : x = (M.op (M.op x y) (M.op x (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1436 eq776
    | exact resolve eq776 eq1436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776 eq1436
  have eq1535 : x = (M.op (M.op x y) (M.op x (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq1528
  have eq1833 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq719 eq1521
    | exact resolve eq1521 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1521
  have eq1850 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq1833
  have eq1899 : (τ (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1850 eq194
    | exact resolve eq194 eq1850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq1930 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1899
    | exact resolve eq1899 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1899
  have eq1995 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1930 eq739
    | exact resolve eq739 eq1930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739 eq1930
  have eq2015 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1995 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1995
  have eq3322 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2015 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2015
    | (have j0 := eq2015 x
       grind)
    | exact resolve eq2015 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2015
  have eq3510 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3322 eq1535
    | exact resolve eq1535 eq3322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535 eq3322
  have eq3523 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq3510
  have eq3555 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3523 eq139
    | exact resolve eq139 eq3523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq3523
  have eq3584 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3555
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3555
    | exact resolve eq3555 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3555
  have eq3891 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3584 eq1850
    | exact resolve eq1850 eq3584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850 eq3584
  have eq3924 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq3891
  have eq3931 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3924 eq26
    | exact resolve eq26 eq3924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3924
  have eq4184 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3931 eq719
    | exact resolve eq719 eq3931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719 eq3931
  have eq4212 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4184
  have eq4218 : x = (M.op x y) := by
    first
    | (have r₁ := eq4212
       have r₂ := eq27
       grind)
    | exact resolve eq4212 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4212
  have eq4220 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq4218 eq20
    | exact resolve eq20 eq4218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq4246 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4220
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4220
    | exact resolve eq4220 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4220
  have eq4249 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq4246 eq26
    | exact resolve eq26 eq4246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4309 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq4249 eq454
    | exact resolve eq454 eq4249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4311 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq4249 eq472
    | exact resolve eq472 eq4249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4249
  have eq4588 : ∀ X0 : G, (σ y) = (M.op (σ (M.op X0 X0)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq4311 (σ X0)
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq4311
    | exact resolve eq4311 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq4311
  have eq4698 : ∀ X0 X1 : G, (M.op (M.op X0 X0) y) = (M.op X1 (M.op X1 (M.op x (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq471 x y X1 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq471
    | (have j0 := eq471 x y X1 X0
       grind)
    | exact resolve eq471 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4741 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ y)) = (M.op X1 (M.op X1 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq471
    | (have j0 := eq471 (σ x) (σ y) X1 X0
       grind)
    | exact resolve eq471 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq471
  have eq4982 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ y)) = (M.op X1 (M.op X1 (M.op (σ (M.op x y)) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq4246 eq4741
    | exact resolve eq4741 eq4246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4741
  have eq4987 : ∀ X0 X1 : G, (M.op (M.op X0 X0) y) = (M.op X1 (M.op X1 (M.op x x))) := by
    intro X0 X1
    first
    | exact superpose eq4218 eq4698
    | exact resolve eq4698 eq4218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4218 eq4698
  have eq15726 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 y)) = (M.op (M.op X2 X2) (M.op X0 (M.op X0 (M.op x x)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq454 X1 y (M.op X2 X2)
       have i₂ := eq4987 X2 X0
       grind)
    | exact superpose eq4987 eq454
    | exact resolve eq454 eq4987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq15805 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op x x)) = (M.op (M.op X1 X1) (M.op (M.op X2 X2) (M.op (M.op X0 X0) y))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq376 (M.op (M.op X3 X3) (M.op x x)) X2 X3 X1
       have i₂ := eq4987 X0 (M.op X3 X3)
       grind)
    | exact superpose eq4987 eq376
    | exact resolve eq376 eq4987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4987
  have eq15862 : ∀ X3 : G, y = (M.op (M.op X3 X3) (M.op x x)) := by
    intro X3
    first
    | (have i₁ := eq15805 x x x X3
       have i₂ := eq376 y x x x
       grind)
    | exact superpose eq376 eq15805
    | exact resolve eq15805 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376 eq15805
  have eq15877 : ∀ X1 : G, (M.op x x) = (M.op X1 (M.op X1 y)) := by
    intro X1
    first
    | (have i₁ := eq15726 x X1 x
       have i₂ := eq472 x (M.op x x) x
       grind)
    | exact superpose eq472 eq15726
    | exact resolve eq15726 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15726
  have eq15957 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq372 x x X1 X0
       have i₂ := eq15862 x
       grind)
    | exact superpose eq15862 eq372
    | exact resolve eq372 eq15862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq16037 : ∀ X0 X1 : G, (M.op y (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq472 X0 X1 (M.op x x)
       have i₂ := eq15862 x
       grind)
    | exact superpose eq15862 eq472
    | exact resolve eq472 eq15862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq16061 : (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq4588 (M.op x x)
       have i₂ := eq15862 x
       grind)
    | exact superpose eq15862 eq4588
    | exact resolve eq4588 eq15862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4588 eq15862
  have eq16094 : (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq16061
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16061
    | exact resolve eq16061 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq16061
  have eq16217 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq16094 eq4982
    | exact resolve eq4982 eq16094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4982 eq16094
  have eq19036 : (M.op (σ y) (σ y)) = (M.op y (σ y)) := by
    first
    | (have i₁ := eq16217 x
       have i₂ := eq15957 x sF3
       grind)
    | exact superpose eq15957 eq16217
    | exact resolve eq16217 eq15957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16217
  have eq19040 : (M.op y y) = (τ (M.op y (σ y))) := by
    first
    | exact superpose eq19036 eq160
    | exact resolve eq160 eq19036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq19107 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq19036 eq15957
    | exact resolve eq15957 eq19036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19036
  have eq19715 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op y (σ y)) (M.op y (σ y))) := by
    first
    | exact superpose eq19040 eq274
    | exact resolve eq274 eq19040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274 eq19040
  have eq19734 : (M.op (M.op y (σ y)) (M.op y (σ y))) = (σ (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq19715
       have i₂ := eq15957 y (M.op y y)
       grind)
    | exact superpose eq15957 eq19715
    | exact resolve eq19715 eq15957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15957 eq19715
  have eq19742 : (σ (M.op x x)) = (M.op (M.op y (σ y)) (M.op y (σ y))) := by
    first
    | (have i₁ := eq19734
       have i₂ := eq15877 y
       grind)
    | exact superpose eq15877 eq19734
    | exact resolve eq19734 eq15877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15877 eq19734
  have eq19744 : (M.op (σ x) (σ x)) = (M.op (M.op y (σ y)) (M.op y (σ y))) := by
    first
    | (have i₁ := eq19742
       have i₂ := eq67
       grind)
    | exact superpose eq67 eq19742
    | exact resolve eq19742 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq19742
  have eq19745 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op y (σ y)) (M.op y (σ y))) := by
    first
    | exact superpose eq4246 eq19744
    | exact resolve eq19744 eq4246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4246 eq19744
  have eq36701 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op y (M.op y (σ y))) := by
    first
    | exact superpose eq19107 eq19745
    | exact resolve eq19745 eq19107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19107 eq19745
  have eq36702 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq4309 eq36701
    | exact resolve eq36701 eq4309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4309 eq36701
  have eq36738 : (M.op (σ x) (σ y)) = (M.op y (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | exact superpose eq36702 eq16037
    | exact resolve eq16037 eq36702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36702
  have eq36741 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36738
       have i₂ := eq16037 sF1 sF1
       grind)
    | exact superpose eq16037 eq36738
    | exact resolve eq36738 eq16037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16037 eq36738
  have eq36758 : False := by grind
  exact eq36758

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(Y,X) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxy_x_pyx_pyx_pxy_Equation731 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq220 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X1) (M.op (M.op X2 X2) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X1 X1) X2
       have i₂ := eq53 (M.op (M.op X1 X1) (M.op (M.op X2 X2) X3)) X0 X1
       grind)
    | (have i₁ := eq9 X3 (M.op X1 X1) X2
       have i₂ := eq53 (M.op (M.op X1 X1) (M.op (M.op X2 X2) X3)) X1 X0
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq124 X0 X0
       have i₂ := eq287 X0
       grind)
    | exact superpose eq287 eq124
    | exact resolve eq124 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq305 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq287 (σ X0)
       grind)
    | exact superpose eq287 eq15
    | exact resolve eq15 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq305 X0
       have i₂ := eq287 X0
       grind)
    | exact superpose eq287 eq305
    | exact resolve eq305 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq307 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq304 X0
       have i₂ := eq287 (τ X0)
       grind)
    | exact superpose eq287 eq304
    | exact resolve eq304 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq316 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) = (σ (M.op (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq306 (M.op X1 X1)
       have i₂ := eq53 (M.op X1 X1) X0 X1
       grind)
    | (have i₁ := eq306 (M.op X1 X1)
       have i₂ := eq53 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq53 eq306
    | exact resolve eq306 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X1 X1))) = (M.op (M.op (σ X1) (σ X1)) (M.op (σ X1) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq316 X0 X0
       have i₂ := eq306 X0
       grind)
    | exact superpose eq306 eq316
    | exact resolve eq316 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq1201 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
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
  have eq1202 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq1201
    | exact resolve eq1201 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201
  have eq1206 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq1202
    | exact resolve eq1202 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202
  have eq1208 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq1206
    | exact resolve eq1206 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206
  have eq1221 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X4 (M.op X4 X1)) := by
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
  have eq1226 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X2) (M.op X3 (M.op (M.op X4 X4) X0)))) = (M.op X3 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X3 (M.op (M.op X4 X4) X0)) X3 X1 X2
       have i₂ := eq9 X0 X3 X4
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1227 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X3) (M.op (M.op X4 X4) (M.op X5 X2))) = (M.op X5 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 (M.op X5 X2) X5 X3 X4
       have i₂ := eq52 X2 X5 X0 X1
       grind)
    | (have i₁ := eq52 (M.op (M.op X3 X3) X0) (M.op X2 X2) X2 X3
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1239 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
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
  clear eq52
  have eq1288 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1221 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1221
    | (have j0 := eq1221 X0 y x
       grind)
    | exact resolve eq1221 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1289 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq1221
    | (have j0 := eq1221 X0 (σ y) (σ x)
       grind)
    | exact resolve eq1221 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1330 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq9 y (M.op X0 X0) X0
       have i₂ := eq1288 (M.op X0 X0)
       grind)
    | exact superpose eq1288 eq9
    | exact resolve eq9 eq1288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1335 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 y))) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1221 X0 (M.op X0 y) X1
       have i₂ := eq1288 X0
       grind)
    | (have i₁ := eq1221 x (M.op x y) x
       have i₂ := eq1288 X0
       grind)
    | exact superpose eq1288 eq1221
    | exact resolve eq1221 eq1288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1341 : ∀ X0 X1 : G, (M.op x (M.op x y)) = (M.op (M.op X1 X1) (M.op (M.op X0 X0) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op X0 X0) y) X1 X0
       have i₂ := eq1288 (M.op X0 X0)
       grind)
    | exact superpose eq1288 eq53
    | exact resolve eq53 eq1288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1356 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1289 eq9
    | exact resolve eq9 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1361 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 (σ y)))) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq1289 eq1221
    | exact resolve eq1221 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1367 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op X1 X1) (M.op (M.op X0 X0) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq1289 eq53
    | exact resolve eq53 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1375 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op x (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1330 (M.op X1 X1)
       have i₂ := eq53 (M.op X1 X1) X0 X1
       grind)
    | (have i₁ := eq1330 (M.op X1 X1)
       have i₂ := eq53 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq53 eq1330
    | exact resolve eq1330 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1330
  have eq1416 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X0 X0) (M.op X1 (M.op x (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1239 X1 (M.op X1 y) X0
       have i₂ := eq1288 X1
       grind)
    | (have i₁ := eq1239 x (M.op x y) x
       have i₂ := eq1288 X0
       grind)
    | exact superpose eq1288 eq1239
    | exact resolve eq1239 eq1288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288
  have eq1467 : ∀ X0 X1 : G, (M.op X1 (M.op x (M.op x y))) = (M.op X1 (M.op X0 (M.op X0 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1335 X1 X1
       have i₂ := eq1221 X1 y X0
       grind)
    | (have i₁ := eq1335 X1 X1
       have i₂ := eq1221 X0 y X1
       grind)
    | exact superpose eq1221 eq1335
    | exact resolve eq1335 eq1221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2011 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (M.op (M.op x (M.op x y)) y) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1416 eq9
    | exact resolve eq9 eq1416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2015 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op x (M.op x y)) y) X1) := by
    intro X0 X1
    first
    | exact superpose eq1416 eq53
    | exact resolve eq53 eq1416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq2016 : (M.op (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y))))) = (σ (M.op (M.op x (M.op x y)) y)) := by
    first
    | exact superpose eq1416 eq306
    | exact resolve eq306 eq1416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1416
  have eq2036 : (σ (M.op (M.op x (M.op x y)) y)) = (M.op (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y))))) := by
    first
    | (have i₁ := eq2016
       have i₂ := eq306 (M.op x sF0)
       grind)
    | exact superpose eq306 eq2016
    | exact resolve eq2016 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2016
  have eq2039 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X1 X1))) = (M.op (M.op (M.op x (M.op x y)) y) (M.op (σ X1) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq330 X0 X1
       have i₂ := eq2015 (σ X1) (M.op (σ X1) (σ X1))
       grind)
    | exact superpose eq2015 eq330
    | exact resolve eq330 eq2015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq2048 : (σ (M.op (M.op x (M.op x y)) y)) = (M.op (M.op (M.op x (M.op x y)) y) (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y))))) := by
    first
    | (have i₁ := eq2036
       have i₂ := eq2015 (σ (M.op x sF0)) (M.op (σ (M.op x sF0)) (σ (M.op x sF0)))
       grind)
    | exact superpose eq2015 eq2036
    | exact resolve eq2036 eq2015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2036
  have eq2635 : ∀ X0 : G, (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) = (σ (M.op (M.op x (M.op x y)) (M.op X0 (M.op X0 y)))) := by
    intro X0
    first
    | exact superpose eq1467 eq306
    | exact resolve eq306 eq1467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467
  have eq3709 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op (M.op (M.op x (M.op x y)) y) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2011 eq1221
    | exact resolve eq1221 eq2011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221 eq2011
  have eq3738 : ∀ X0 X1 : G, (M.op (M.op (M.op x (M.op x y)) y) X1) = (M.op (M.op (M.op (M.op x (M.op x y)) y) (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2015 (M.op X0 X0) X1
       have i₂ := eq2015 X0 (M.op X0 X0)
       grind)
    | exact superpose eq2015 eq2015
    | exact resolve eq2015 eq2015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3943 : ∀ X0 : G, (M.op (σ (M.op (M.op x (M.op x y)) y)) (σ (M.op (M.op x (M.op x y)) y))) = (σ (M.op (M.op X0 X0) (M.op (M.op x (M.op x y)) y))) := by
    intro X0
    first
    | exact superpose eq2015 eq306
    | exact resolve eq306 eq2015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3955 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) (M.op (M.op x (M.op x y)) y))) (M.op x (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq2015 eq1375
    | exact resolve eq1375 eq2015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375
  have eq4066 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op (M.op x (M.op x y)) y))) = (M.op (M.op (M.op (M.op x (M.op x y)) y) (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y))))) (M.op (M.op (M.op x (M.op x y)) y) (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))))) := by
    intro X0
    first
    | exact superpose eq2048 eq3943
    | exact resolve eq3943 eq2048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3943
  have eq4281 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op (M.op x (M.op x y)) y))) = (M.op (M.op (M.op x (M.op x y)) y) (M.op (M.op (M.op x (M.op x y)) y) (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))))) := by
    intro X0
    first
    | exact superpose eq3738 eq4066
    | exact resolve eq4066 eq3738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3738 eq4066
  have eq7551 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) X2) = (M.op (M.op (M.op X3 X3) (M.op (M.op X0 X0) (M.op (M.op x (M.op x y)) y))) X2) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq2015 eq209
    | exact resolve eq209 eq2015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7561 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op y (M.op x (M.op x y))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq209 y (M.op y y) X0 X1
       have i₂ := eq1335 y (M.op y y)
       grind)
    | exact superpose eq1335 eq209
    | exact resolve eq209 eq1335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq8381 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 (M.op (M.op x (M.op x y)) y))) X1) = (M.op (M.op y (M.op x (M.op x y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq1335 eq7561
    | exact resolve eq7561 eq1335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335
  have eq8488 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op (M.op y (M.op x (M.op x y))) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq7561 x X0
       grind)
    | exact superpose eq7561 eq9
    | exact resolve eq9 eq7561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8493 : ∀ X0 : G, (M.op (M.op (M.op x (M.op x y)) y) X0) = (M.op (M.op y (M.op x (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq2015 x X0
       have i₂ := eq7561 x X0
       grind)
    | exact superpose eq7561 eq2015
    | exact resolve eq2015 eq7561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2015
  have eq8499 : ∀ X0 X1 : G, (M.op (M.op y (M.op x (M.op x y))) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1239 X0 X1 x
       have i₂ := eq7561 x (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq7561 eq1239
    | exact resolve eq1239 eq7561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7561
  have eq9061 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op (M.op y (M.op x (M.op x y))) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq8493 eq3709
    | exact resolve eq3709 eq8493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3709
  have eq9152 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op (M.op x (M.op x y)) y))) = (M.op (M.op y (M.op x (M.op x y))) (M.op (M.op (M.op x (M.op x y)) y) (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))))) := by
    intro X0
    first
    | exact superpose eq8493 eq4281
    | exact resolve eq4281 eq8493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4281
  have eq9161 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X1 X1))) = (M.op (M.op y (M.op x (M.op x y))) (M.op (σ X1) (σ X1))) := by
    intro X0 X1
    first
    | exact superpose eq8493 eq2039
    | exact resolve eq2039 eq8493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2039
  have eq9162 : (σ (M.op (M.op x (M.op x y)) y)) = (M.op (M.op y (M.op x (M.op x y))) (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y))))) := by
    first
    | exact superpose eq8493 eq2048
    | exact resolve eq2048 eq8493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2048
  have eq9410 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op (M.op x (M.op x y)) y))) = (M.op (M.op y (M.op x (M.op x y))) (M.op (M.op y (M.op x (M.op x y))) (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))))) := by
    intro X0
    first
    | exact superpose eq8493 eq9152
    | exact resolve eq9152 eq8493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8493 eq9152
  have eq17926 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1208
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq1208
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq1208 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17950 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq17926
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17926
    | exact resolve eq17926 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17926
  have eq17953 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq17950
    | exact resolve eq17950 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17950
  have eq17954 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq17953
       have r₂ := eq27
       grind)
    | exact resolve eq17953 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17953
  have eq17955 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq17954
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17954
    | exact resolve eq17954 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17954
  have eq17956 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq17955
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17955
    | exact resolve eq17955 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17955
  have eq17958 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq17956 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq17956
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq17956
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq17956
       grind)
    | exact resolve eq12 eq17956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17956
  have eq17970 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq17958
       have r₂ := eq26
       grind)
    | exact resolve eq17958 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17958
  have eq17973 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq61 eq17970
    | exact resolve eq17970 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17970
  have eq17976 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq17973
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq17973
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq17973 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17973
  have eq18000 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq17976
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17976
    | exact resolve eq17976 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17976
  have eq18003 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq18000
    | exact resolve eq18000 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18000
  have eq18004 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq18003
       have r₂ := eq27
       grind)
    | exact resolve eq18003 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18003
  have eq18005 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq18004
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18004
    | exact resolve eq18004 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18004
  have eq18006 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq18005
  have eq18007 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq18006
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18006
    | exact resolve eq18006 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18006
  have eq18008 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18007
  have eq18010 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18008
       grind)
    | exact superpose eq18008 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq18008
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq18008
       grind)
    | exact resolve eq12 eq18008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18008
  have eq18022 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq18010
       have r₂ := eq18
       grind)
    | exact resolve eq18010 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq18010
  have eq18028 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1208
       have i₂ := eq18022
       grind)
    | exact superpose eq18022 eq1208
    | exact resolve eq1208 eq18022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq18032 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq18028
  have eq18035 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq18032
    | exact resolve eq18032 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18032
  have eq18037 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18035
       have r₂ := eq27
       grind)
    | exact resolve eq18035 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18035
  have eq18061 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18037 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq18037
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq18037
       grind)
    | exact resolve eq12 eq18037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18037
  have eq18073 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18061
       have r₂ := eq26
       grind)
    | exact resolve eq18061 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18061
  have eq18076 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq61 eq18073
    | exact resolve eq18073 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq18073
  have eq18079 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18076
       have i₂ := eq18022
       grind)
    | exact superpose eq18022 eq18076
    | exact resolve eq18076 eq18022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18022 eq18076
  have eq18102 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18079
  have eq18106 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq18102
    | exact resolve eq18102 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18102
  have eq18110 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18106
       have r₂ := eq27
       grind)
    | exact resolve eq18106 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18106
  have eq20081 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op X0 (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18110 eq1289
    | exact resolve eq1289 eq18110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1289 eq18110
  have eq20190 : ∀ X0 : G, (τ (M.op X0 (M.op X0 (σ y)))) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20081 eq307
    | exact resolve eq307 eq20081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20211 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op X0 (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20081 eq1356
    | exact resolve eq1356 eq20081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20262 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op X0 (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20081 eq1361
    | exact resolve eq1361 eq20081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1361 eq20081
  have eq20342 : ∀ X0 : G, (M.op x x) = (τ (M.op X0 (M.op X0 (σ y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq38 eq20190
    | exact resolve eq20190 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20190
  have eq23032 : (M.op x x) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1367 eq20342
    | (have j0 := eq20342 (σ x)
       grind)
    | exact resolve eq20342 eq1367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20342
  have eq23682 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X5 X5) X0)) = (M.op (M.op X1 X1) (M.op (M.op X2 X2) (M.op X3 (M.op (M.op X4 X4) (M.op (M.op y (M.op x (M.op x y))) X0))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | exact superpose eq8488 eq1227
    | exact resolve eq1227 eq8488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8488
  have eq23716 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X4 (M.op X0 X1)) = (M.op (M.op X2 X2) (M.op (M.op X3 X3) (M.op X4 (M.op X0 (M.op (M.op X5 X5) X1))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1227 x x (M.op X0 (M.op (M.op X5 X5) X1)) X2 X3 X4
       have i₂ := eq1226 X1 x x X0 X5
       grind)
    | exact superpose eq1226 eq1227
    | exact resolve eq1227 eq1226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23826 : ∀ X0 X1 X2 X3 X4 X5 X6 X8 : G, (M.op X6 (M.op (M.op X8 X8) (M.op X0 X3))) = (M.op (M.op X4 X4) (M.op (M.op X5 X5) (M.op X6 (M.op X0 (M.op (M.op X1 X1) (M.op (M.op X2 X2) X3)))))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X8
    first
    | (have i₁ := eq1226 (M.op (M.op X8 X8) (M.op X0 X3)) X4 X5 X6 x
       have i₂ := eq1227 X1 X2 X3 x X8 X0
       grind)
    | (have i₁ := eq1226 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) X1 X2 X3 X4
       have i₂ := eq1227 X0 X1 X2 X3 X4 (M.op X4 X4)
       grind)
    | exact superpose eq1227 eq1226
    | exact resolve eq1226 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227
  have eq24503 : ∀ X0 X2 X3 X6 X8 : G, (M.op X6 (M.op (M.op X8 X8) (M.op X0 X3))) = (M.op X6 (M.op X0 (M.op (M.op X2 X2) X3))) := by
    intro X0 X2 X3 X6 X8
    first
    | (have i₁ := eq23826 X0 x X2 X3 x x X6 X8
       have i₂ := eq23716 X0 (M.op (M.op X2 X2) X3) x x X6 x
       grind)
    | exact superpose eq23716 eq23826
    | exact resolve eq23826 eq23716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23716 eq23826
  have eq24535 : ∀ X0 X3 X5 : G, (M.op X3 (M.op (M.op y (M.op x (M.op x y))) X0)) = (M.op X3 (M.op (M.op X5 X5) X0)) := by
    intro X0 X3 X5
    first
    | (have i₁ := eq23682 X0 x x X3 x X5
       have i₂ := eq1226 (M.op (M.op y (M.op x sF0)) X0) x x X3 x
       grind)
    | exact superpose eq1226 eq23682
    | exact resolve eq23682 eq1226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226 eq23682
  have eq25262 : (σ y) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1367 eq20211
    | (have j0 := eq20211 (σ x)
       grind)
    | exact resolve eq20211 eq1367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367 eq20211
  have eq27688 : (σ y) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20262 eq25262
    | exact resolve eq25262 eq20262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20262 eq25262
  have eq27697 : (σ y) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq27688
  have eq27780 : (σ y) ≠ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ y) = (k (M.op (σ x) (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27697 eq12
    | exact resolve eq12 eq27697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27697
  have eq27802 : (σ y) = (k (M.op (σ x) (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq27780
       have r₂ := eq1356 (σ x)
       grind)
    | exact resolve eq27780 eq1356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1356 eq27780
  have eq27835 : (τ (σ y)) = (k (τ (M.op (σ x) (σ x))) (τ (M.op (σ x) (M.op (σ x) (σ y))))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27802 eq124
    | exact resolve eq124 eq27802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq27802
  have eq27840 : (τ (σ y)) = (k (M.op (τ (σ x)) (τ (σ x))) (τ (M.op (σ x) (M.op (σ x) (σ y))))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27835
       have i₂ := eq307 sF2
       grind)
    | exact superpose eq307 eq27835
    | exact resolve eq27835 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307 eq27835
  have eq27845 : (τ (σ y)) = (k (M.op x x) (τ (M.op (σ x) (M.op (σ x) (σ y))))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq27840
    | exact resolve eq27840 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq27840
  have eq27847 : y = (k (M.op x x) (τ (M.op (σ x) (M.op (σ x) (σ y))))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39 eq27845
    | exact resolve eq27845 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq27845
  have eq27879 : y = (k (M.op x x) (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23032 eq27847
    | exact resolve eq27847 eq23032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23032 eq27847
  have eq27895 : y = (k (M.op x x) (M.op x x)) ∨ x = (M.op x y) := by grind
  clear eq27879
  have eq27912 : y = (M.op (M.op x x) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27895
       have i₂ := eq287 (M.op x x)
       grind)
    | exact superpose eq287 eq27895
    | exact resolve eq27895 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287 eq27895
  have eq28054 : ∀ X0 : G, (M.op x x) = (M.op (M.op X0 X0) (M.op (M.op x x) y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1239 (M.op x x) (M.op x x) X0
       have i₂ := eq27912
       grind)
    | exact superpose eq27912 eq1239
    | exact resolve eq1239 eq27912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27912
  have eq28076 : (M.op x x) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28054 x
       have i₂ := eq1341 x x
       grind)
    | exact superpose eq1341 eq28054
    | exact resolve eq28054 eq1341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341 eq28054
  have eq28999 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 X0) (M.op x (M.op x x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28076 eq1239
    | exact resolve eq1239 eq28076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28076
  have eq29012 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28999 x
       have i₂ := eq1239 x x x
       grind)
    | exact superpose eq1239 eq28999
    | exact resolve eq28999 eq1239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28999
  have eq29013 : x = (M.op x y) := by grind
  clear eq29012
  have eq29015 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq29013 eq20
    | exact resolve eq20 eq29013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq29277 : ∀ X0 : G, (M.op (σ (M.op x x)) (σ (M.op x x))) = (σ (M.op (M.op x x) (M.op X0 (M.op X0 y)))) := by
    intro X0
    first
    | exact superpose eq29013 eq2635
    | exact resolve eq2635 eq29013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2635
  have eq29337 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) (M.op (M.op x x) y))) (M.op x x)) := by
    intro X0 X1
    first
    | exact superpose eq29013 eq3955
    | exact resolve eq3955 eq29013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3955
  have eq29497 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) X2) = (M.op (M.op (M.op X3 X3) (M.op (M.op X0 X0) (M.op (M.op x x) y))) X2) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq29013 eq7551
    | exact resolve eq7551 eq29013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7551
  have eq29502 : ∀ X0 X1 : G, (M.op (M.op y (M.op x x)) X1) = (M.op (M.op X0 (M.op X0 (M.op (M.op x x) y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq29013 eq8381
    | exact resolve eq8381 eq29013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8381
  have eq29515 : ∀ X0 X1 : G, (M.op (M.op y (M.op x x)) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq29013 eq8499
    | exact resolve eq8499 eq29013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8499
  have eq29552 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op (M.op y (M.op x x)) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq29013 eq9061
    | exact resolve eq9061 eq29013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9061
  have eq29583 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X1 X1))) = (M.op (M.op y (M.op x x)) (M.op (σ X1) (σ X1))) := by
    intro X0 X1
    first
    | exact superpose eq29013 eq9161
    | exact resolve eq9161 eq29013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9161
  have eq29584 : (σ (M.op (M.op x x) y)) = (M.op (M.op y (M.op x x)) (M.op (σ (M.op x x)) (σ (M.op x x)))) := by
    first
    | exact superpose eq29013 eq9162
    | exact resolve eq9162 eq29013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9162
  have eq29590 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op (M.op x x) y))) = (M.op (M.op y (M.op x x)) (M.op (M.op y (M.op x x)) (M.op (σ (M.op x x)) (σ (M.op x x))))) := by
    intro X0
    first
    | exact superpose eq29013 eq9410
    | exact resolve eq9410 eq29013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9410
  have eq30165 : ∀ X0 X3 X5 : G, (M.op X3 (M.op (M.op X5 X5) X0)) = (M.op X3 (M.op (M.op y (M.op x x)) X0)) := by
    intro X0 X3 X5
    first
    | exact superpose eq29013 eq24535
    | exact resolve eq24535 eq29013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24535 eq29013
  have eq30410 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op (M.op x x) y))) = (M.op (M.op y (M.op x x)) (M.op (M.op y (M.op x x)) (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))))) := by
    intro X0
    first
    | (have i₁ := eq29590 X0
       have i₂ := eq306 x
       grind)
    | exact superpose eq306 eq29590
    | exact resolve eq29590 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29590
  have eq30412 : (σ (M.op (M.op x x) y)) = (M.op (M.op y (M.op x x)) (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq29584
       have i₂ := eq306 x
       grind)
    | exact superpose eq306 eq29584
    | exact resolve eq29584 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29584
  have eq30417 : ∀ X1 : G, (M.op y X1) = (M.op (M.op y (M.op x x)) X1) := by
    intro X1
    first
    | (have i₁ := eq29502 x X1
       have i₂ := eq9 y x x
       grind)
    | exact superpose eq9 eq29502
    | exact resolve eq29502 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29502
  have eq30419 : ∀ X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op y X2) := by
    intro X1 X2
    first
    | (have i₁ := eq29497 x X1 X2 x
       have i₂ := eq220 x x x y
       grind)
    | exact superpose eq220 eq29497
    | exact resolve eq29497 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29497
  have eq30474 : y = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq29337 x x
       have i₂ := eq220 x x x y
       grind)
    | exact superpose eq220 eq29337
    | exact resolve eq29337 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq29337
  have eq30487 : (σ y) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq29277 x
       have i₂ := eq1239 x y x
       grind)
    | exact superpose eq1239 eq29277
    | exact resolve eq29277 eq1239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239 eq29277
  have eq30559 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq29015
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29015
    | exact resolve eq29015 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29015
  have eq30632 : ∀ X0 : G, (M.op (σ x) (σ x)) = (σ (M.op (M.op X0 X0) (M.op (M.op x x) y))) := by
    intro X0
    first
    | (have i₁ := eq30410 X0
       have i₂ := eq9 (M.op (σ x) (σ x)) (M.op y (M.op x x)) (σ x)
       grind)
    | exact superpose eq9 eq30410
    | exact resolve eq30410 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30410
  have eq30634 : (σ (M.op (M.op x x) y)) = (M.op (M.op y (M.op x x)) (M.op (M.op y (M.op x x)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq30412
       have i₂ := eq30165 (M.op (σ x) (σ x)) (M.op y (M.op x x)) (σ x)
       grind)
    | exact superpose eq30165 eq30412
    | exact resolve eq30412 eq30165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30165 eq30412
  have eq30658 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op y X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29552 X0 X1 X2
       have i₂ := eq30417 X0
       grind)
    | exact superpose eq30417 eq29552
    | exact resolve eq29552 eq30417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29552
  have eq30720 : ∀ X0 X1 : G, (M.op y (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29515 X0 X1
       have i₂ := eq30417 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq30417 eq29515
    | exact resolve eq29515 eq30417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29515
  have eq30870 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X1 X1))) = (M.op y (M.op (σ X1) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29583 X0 X1
       have i₂ := eq30417 (M.op (σ X1) (σ X1))
       grind)
    | exact superpose eq30417 eq29583
    | exact resolve eq29583 eq30417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29583 eq30417
  have eq31150 : ∀ X0 X3 X6 X8 : G, (M.op X6 (M.op (M.op X8 X8) (M.op X0 X3))) = (M.op X6 (M.op X0 (M.op y X3))) := by
    intro X0 X3 X6 X8
    first
    | (have i₁ := eq24503 X0 x X3 X6 X8
       have i₂ := eq30419 x X3
       grind)
    | exact superpose eq30419 eq24503
    | exact resolve eq24503 eq30419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24503
  have eq31539 : (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq30487
       have i₂ := eq306 x
       grind)
    | exact superpose eq306 eq30487
    | exact resolve eq30487 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30487
  have eq31600 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq30559 eq22
    | exact resolve eq22 eq30559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq31601 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq30559 eq26
    | exact resolve eq26 eq30559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq30559
  have eq32192 : (M.op (σ x) (σ x)) = (σ (M.op y (M.op (M.op x x) y))) := by
    first
    | (have i₁ := eq30632 x
       have i₂ := eq30419 x (M.op (M.op x x) y)
       grind)
    | exact superpose eq30419 eq30632
    | exact resolve eq30632 eq30419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30632
  have eq32194 : (σ (M.op (M.op x x) y)) = (M.op y (M.op y (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq30634
       have i₂ := eq30474
       grind)
    | exact superpose eq30474 eq30634
    | exact resolve eq30634 eq30474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30474 eq30634
  have eq32246 : ∀ X1 : G, (M.op y (M.op (σ X1) (σ X1))) = (σ (M.op y (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq30870 x X1
       have i₂ := eq30419 x (M.op X1 X1)
       grind)
    | exact superpose eq30419 eq30870
    | exact resolve eq30870 eq30419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30870
  have eq32819 : ∀ X0 X3 X6 : G, (M.op X6 (M.op X0 (M.op y X3))) = (M.op X6 (M.op y (M.op X0 X3))) := by
    intro X0 X3 X6
    first
    | (have i₁ := eq31150 X0 X3 X6 x
       have i₂ := eq30419 x (M.op X0 X3)
       grind)
    | exact superpose eq30419 eq31150
    | exact resolve eq31150 eq30419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31150
  have eq33055 : (σ y) = (M.op y (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq31539
       have i₂ := eq30419 (σ x) (M.op (σ x) (σ x))
       grind)
    | exact superpose eq30419 eq31539
    | exact resolve eq31539 eq30419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31539
  have eq33363 : (M.op (σ x) (σ x)) = (σ (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq32192
       have i₂ := eq30419 x y
       grind)
    | exact superpose eq30419 eq32192
    | exact resolve eq32192 eq30419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32192
  have eq33365 : (σ (M.op (M.op x x) y)) = (M.op y (M.op y (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | (have i₁ := eq32194
       have i₂ := eq31600
       grind)
    | exact superpose eq31600 eq32194
    | exact resolve eq32194 eq31600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32194
  have eq34077 : (σ y) = (M.op y (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq33055
       have i₂ := eq31600
       grind)
    | exact superpose eq31600 eq33055
    | exact resolve eq33055 eq31600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33055
  have eq34316 : (M.op (σ x) (σ x)) = (M.op y (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq33363
       have i₂ := eq32246 y
       grind)
    | exact superpose eq32246 eq33363
    | exact resolve eq33363 eq32246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32246 eq33363
  have eq34318 : (σ (M.op y y)) = (M.op y (M.op y (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | (have i₁ := eq33365
       have i₂ := eq30419 x y
       grind)
    | exact superpose eq30419 eq33365
    | exact resolve eq33365 eq30419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30419 eq33365
  have eq34739 : (σ y) = (M.op y (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq34077
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq34077
    | exact resolve eq34077 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34077
  have eq34836 : (M.op (σ x) (σ x)) = (M.op y (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq34316
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq34316
    | exact resolve eq34316 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34316
  have eq34838 : (M.op (σ y) (σ y)) = (M.op y (M.op y (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | (have i₁ := eq34318
       have i₂ := eq306 y
       grind)
    | exact superpose eq306 eq34318
    | exact resolve eq34318 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq34318
  have eq35127 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op y (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq34836
       have i₂ := eq31600
       grind)
    | exact superpose eq31600 eq34836
    | exact resolve eq34836 eq31600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31600 eq34836
  have eq35128 : (M.op (σ y) (σ y)) = (M.op y (σ y)) := by
    first
    | exact superpose eq34739 eq34838
    | exact resolve eq34838 eq34739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34739 eq34838
  have eq35300 : (M.op (σ y) (σ y)) = (M.op y (σ y)) := by
    first
    | (have i₁ := eq35128
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35128
    | exact resolve eq35128 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq35128
  have eq35397 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op y (M.op y (σ y))) := by
    first
    | exact superpose eq35300 eq35127
    | exact resolve eq35127 eq35300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35127 eq35300
  have eq36064 : (σ (M.op x y)) = (M.op y (M.op (σ (M.op x y)) (M.op y (M.op y (σ y))))) := by
    first
    | exact superpose eq35397 eq30720
    | exact resolve eq30720 eq35397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30720 eq35397
  have eq36069 : (σ (M.op x y)) = (M.op y (M.op y (M.op (σ (M.op x y)) (M.op y (σ y))))) := by
    first
    | (have i₁ := eq36064
       have i₂ := eq32819 sF1 (M.op y sF3) y
       grind)
    | exact superpose eq32819 eq36064
    | exact resolve eq36064 eq32819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32819 eq36064
  have eq36077 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq36069
       have i₂ := eq30658 sF3 y sF1
       grind)
    | exact superpose eq30658 eq36069
    | exact resolve eq36069 eq30658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30658 eq36069
  have eq36081 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31601 eq36077
    | exact resolve eq36077 eq31601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31601 eq36077
  have eq36085 : False := by grind
  exact eq36085

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pxx_x_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
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
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq43 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq23 (σ X0)
       grind)
    | exact superpose eq23 eq15
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq43 X0
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq43
    | exact resolve eq43 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq43
  have eq135 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X2 X2) x
       have i₂ := eq20 X1 X0 X2 x
       grind)
    | (have i₁ := eq9 X0 (M.op X2 X2) X2
       have i₂ := eq20 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq284 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq26
    | (have j0 := eq26 X0 X1
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq26 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq327 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq284 X0 X1
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq284
    | (have j0 := eq284 X0 X1
       grind)
    | exact resolve eq284 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq867 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 X1) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq135 (σ X0) (σ X0) X1
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq135
    | exact resolve eq135 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33824 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq327 x y
       grind)
    | exact superpose eq327 eq16
    | (have j1 := eq327 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq327 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq327 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq327 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq34086 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq33824
  have eq37217 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (σ (M.op x x)))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq135 (σ x) (σ y) X0
       have i₂ := eq34086
       grind)
    | exact superpose eq34086 eq135
    | exact resolve eq135 eq34086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34086
  have eq37270 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq37217 x
       have i₂ := eq867 x x
       grind)
    | exact superpose eq867 eq37217
    | exact resolve eq37217 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867 eq37217
  have eq37271 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq37270
  have eq52793 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x (M.op x x))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq135 x y X0
       have i₂ := eq37271
       grind)
    | exact superpose eq37271 eq135
    | exact resolve eq135 eq37271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37271
  have eq52861 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq52793 x
       have i₂ := eq135 x x x
       grind)
    | exact superpose eq135 eq52793
    | exact resolve eq52793 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq52793
  have eq52862 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq52861
  have eq63938 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq52862
       grind)
    | exact superpose eq52862 eq10
    | exact resolve eq10 eq52862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52862
  have eq64020 : x = y ∨ x = y := by
    first
    | (have i₁ := eq63938
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq63938
    | exact resolve eq63938 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63938
  have eq64021 : x = y := by grind
  clear eq64020
  have eq84332 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq64021
       grind)
    | exact superpose eq64021 eq16
    | exact resolve eq16 eq64021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64021
  have eq84333 : False := by grind
  exact eq84333

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_x_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq14 (M.op X1 X0) (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq44 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq44
    | (have j0 := eq44 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq44 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq35 (τ X0)
       grind)
    | exact superpose eq35 eq19
    | exact resolve eq19 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq83 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82
    | exact resolve eq82 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq83
    | exact resolve eq83 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq83
  have eq95 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq91 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq91
    | exact resolve eq91 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq179 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq57 y x
       grind)
    | exact superpose eq57 eq16
    | (have j1 := eq57 x y
       grind)
    | exact resolve eq16 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq275 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq179
       have i₂ := eq44 y x
       grind)
    | exact superpose eq44 eq179
    | (have j1 := eq44 (σ x) (σ y)
       grind)
    | (have r₁ := eq179
       have r₂ := eq44 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq179
       have r₂ := eq44 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq179 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq179
  have eq276 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq275
  have eq277 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq276
       grind)
    | exact superpose eq276 eq16
    | exact resolve eq16 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq278 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq277
       have r₂ := eq95 x
       grind)
    | exact resolve eq277 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq309 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq278
       grind)
    | exact superpose eq278 eq10
    | exact resolve eq10 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq328 : x = y := by
    first
    | (have i₁ := eq309
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq309
    | exact resolve eq309 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq367 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq328
       grind)
    | exact superpose eq328 eq16
    | exact resolve eq16 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq368 : False := by grind
  exact eq368

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pyx_pxx_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq24 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq26 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq24 (τ X0)
       grind)
    | exact superpose eq24 eq19
    | (have j1 := eq24 (τ X0)
       grind)
    | exact resolve eq19 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq24
  have eq120 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq116 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq116
    | (have j0 := eq116 X0
       grind)
    | exact resolve eq116 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq124 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq120 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq120
    | (have j0 := eq120 X0
       grind)
    | exact resolve eq120 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq128 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq124 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq124 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq124 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq146 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq26
    | (have j0 := eq26 X0 X1
       have j1 := eq14 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq26 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq128 (σ X0)
       grind)
    | exact superpose eq128 eq15
    | exact resolve eq15 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq167 X0
       have i₂ := eq128 X0
       grind)
    | exact superpose eq128 eq167
    | exact resolve eq167 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq167
  have eq6421 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq146 x y
       grind)
    | exact superpose eq146 eq16
    | (have j1 := eq146 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq146 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq146 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq146 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq6446 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq6421
  have eq6833 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6446
       grind)
    | exact superpose eq6446 eq16
    | exact resolve eq16 eq6446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6834 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq6446
       grind)
    | exact superpose eq6446 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq6446
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq6446
       grind)
    | exact resolve eq12 eq6446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6446
  have eq6849 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq6834
  have eq6853 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6849
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq6849
    | exact resolve eq6849 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6849
  have eq16714 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6853
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq6853
    | (have j1 := eq14 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq6853 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6853
  have eq16743 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq16714
  have eq16756 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq16743
       have r₂ := eq6833
       grind)
    | exact resolve eq16743 eq6833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6833 eq16743
  have eq32314 : y ≠ y ∨ y = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq16756
       grind)
    | exact superpose eq16756 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq16756
       grind)
    | exact resolve eq12 eq16756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32346 : y = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq32314
  have eq58697 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26 x y
       have i₂ := eq32346
       grind)
    | exact superpose eq32346 eq26
    | (have j0 := eq26 x y
       grind)
    | exact resolve eq26 eq32346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq32346
  have eq58700 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq58697
  have eq88523 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq58700
       grind)
    | exact superpose eq58700 eq16
    | exact resolve eq16 eq58700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58700
  have eq122901 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq88523
       have i₂ := eq16756
       grind)
    | exact superpose eq16756 eq88523
    | exact resolve eq88523 eq16756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16756 eq88523
  have eq122902 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq122901
  have eq122903 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq122902
  have eq147241 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq122903
       grind)
    | exact superpose eq122903 eq10
    | exact resolve eq10 eq122903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122903
  have eq147276 : x = y ∨ x = y := by
    first
    | (have i₁ := eq147241
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq147241
    | exact resolve eq147241 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147241
  have eq147277 : x = y := by grind
  clear eq147276
  have eq151431 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq147277
       grind)
    | exact superpose eq147277 eq16
    | exact resolve eq16 eq147277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147277
  have eq151432 : False := by grind
  exact eq151432

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pxy_pxx_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq30 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 X0 x
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
  have eq56 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
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
    | (have r₁ := eq234 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq234 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq270 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq56
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq274 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq270
    | exact resolve eq270 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq276 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq274
    | exact resolve eq274 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq278 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq276
    | exact resolve eq276 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
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
  clear eq124
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
  clear eq52
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
  have eq1072 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq9 y (M.op X0 X0) X0
       have i₂ := eq1028 (M.op X0 X0)
       grind)
    | exact superpose eq1028 eq9
    | exact resolve eq9 eq1028
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
  clear eq961
  have eq1100 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1029 eq9
    | exact resolve eq9 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
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
  clear eq1028
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
  have eq3307 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 X0)) = (M.op X2 (M.op (M.op (M.op x (M.op x y)) y) X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1755 eq979
    | exact resolve eq979 eq1755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3913 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (M.op x (M.op x y)) y) X0)) = (M.op (M.op (M.op x (M.op x y)) y) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq1755 eq1763
    | exact resolve eq1763 eq1755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1755 eq1763
  have eq8377 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op y (M.op x (M.op x y))) X1) := by
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
  have eq9421 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op (M.op y (M.op x (M.op x y))) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq8377 x X0
       grind)
    | exact superpose eq8377 eq9
    | exact resolve eq9 eq8377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9426 : ∀ X0 : G, (M.op (M.op (M.op x (M.op x y)) y) X0) = (M.op (M.op y (M.op x (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq1760 x X0
       have i₂ := eq8377 x X0
       grind)
    | exact superpose eq8377 eq1760
    | exact resolve eq1760 eq8377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1760 eq8377
  have eq10084 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 X0)) = (M.op X2 (M.op (M.op y (M.op x (M.op x y))) X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq9426 eq3307
    | exact resolve eq3307 eq9426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3307
  have eq10106 : ∀ X0 X1 : G, (M.op (M.op (M.op x (M.op x y)) y) (M.op X1 X0)) = (M.op X1 (M.op (M.op y (M.op x (M.op x y))) X0)) := by
    intro X0 X1
    first
    | exact superpose eq9426 eq3913
    | exact resolve eq3913 eq9426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3913
  have eq10564 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op y (M.op x (M.op x y))) X0)) = (M.op (M.op y (M.op x (M.op x y))) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq9426 eq10106
    | exact resolve eq10106 eq9426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9426 eq10106
  have eq13649 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq278
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq278
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq278 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq13667 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13649
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13649
    | exact resolve eq13649 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13649
  have eq13670 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq13667
    | exact resolve eq13667 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13667
  have eq13671 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq13670
       have r₂ := eq27
       grind)
    | exact resolve eq13670 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13670
  have eq13672 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13671
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13671
    | exact resolve eq13671 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13671
  have eq13673 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13672
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13672
    | exact resolve eq13672 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13672
  have eq13718 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq13673 eq979
    | exact resolve eq979 eq13673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13673
  have eq13729 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1100 eq13718
    | exact resolve eq13718 eq1100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13718
  have eq15030 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op x (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq979 x x X0
       have i₂ := eq13729
       grind)
    | exact superpose eq13729 eq979
    | exact resolve eq979 eq13729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979 eq13729
  have eq15041 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1072 eq15030
    | exact resolve eq15030 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15030
  have eq15050 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq15041 eq1100
    | exact resolve eq1100 eq15041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100 eq15041
  have eq21063 : (τ (σ y)) = (M.op (τ (M.op (σ x) (σ x))) (τ (M.op (σ x) (σ x)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq15050 eq285
    | exact resolve eq285 eq15050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15050
  have eq21144 : (τ (σ y)) = (M.op (M.op (τ (σ x)) (τ (σ x))) (M.op (τ (σ x)) (τ (σ x)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq21063
       have i₂ := eq285 sF2
       grind)
    | exact superpose eq285 eq21063
    | exact resolve eq21063 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285 eq21063
  have eq21171 : (τ (σ y)) = (M.op (τ (σ x)) (M.op (M.op y (M.op x (M.op x y))) (τ (σ x)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq21144
       have i₂ := eq10084 (τ sF2) (τ sF2) (τ sF2)
       grind)
    | exact superpose eq10084 eq21144
    | exact resolve eq21144 eq10084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21144
  have eq21187 : (τ (σ y)) = (M.op (M.op y (M.op x (M.op x y))) (M.op (τ (σ x)) (τ (σ x)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq10564 eq21171
    | exact resolve eq21171 eq10564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21171
  have eq21190 : (τ (σ y)) = (M.op (M.op y (M.op x (M.op x y))) (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq38 eq21187
    | exact resolve eq21187 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21187
  have eq21192 : (τ (σ y)) = (M.op x (M.op (M.op y (M.op x (M.op x y))) x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq10564 eq21190
    | exact resolve eq21190 eq10564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21190
  have eq21193 : y = (M.op x (M.op (M.op y (M.op x (M.op x y))) x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq39 eq21192
    | exact resolve eq21192 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21192
  have eq158125 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21193 eq9421
    | exact resolve eq9421 eq21193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21193
  have eq158138 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq158125
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq158125
    | exact resolve eq158125 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158125
  have eq158139 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq158138
  have eq158148 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq158139 eq39
    | exact resolve eq39 eq158139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq158139
  have eq158248 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq38 eq158148
    | exact resolve eq158148 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq158148
  have eq158249 : x = (M.op x y) ∨ x = y := by grind
  clear eq158248
  have eq158259 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq158249 eq20
    | exact resolve eq20 eq158249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158267 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq158249 eq1072
    | exact resolve eq1072 eq158249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072 eq158249
  have eq158293 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq158259
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq158259
    | exact resolve eq158259 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158259
  have eq161465 : (σ y) = (M.op (σ (M.op x x)) (σ (M.op x x))) ∨ x = y := by
    first
    | (have i₁ := eq284 (M.op x x)
       have i₂ := eq158267 x
       grind)
    | exact superpose eq158267 eq284
    | exact resolve eq284 eq158267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158267
  have eq161703 : (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq161465
       have i₂ := eq284 x
       grind)
    | exact superpose eq284 eq161465
    | exact resolve eq161465 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161465
  have eq161738 : (σ y) = (M.op (σ x) (M.op (M.op y (M.op x (M.op x y))) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq161703
       have i₂ := eq10084 (σ x) (σ x) (σ x)
       grind)
    | exact superpose eq10084 eq161703
    | exact resolve eq161703 eq10084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10084 eq161703
  have eq161761 : (σ y) = (M.op (M.op y (M.op x (M.op x y))) (M.op (σ x) (σ x))) ∨ x = y := by
    first
    | exact superpose eq10564 eq161738
    | exact resolve eq161738 eq10564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161738
  have eq161763 : (σ y) = (M.op (M.op y (M.op x (M.op x y))) (M.op (σ x) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq161761
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq161761
    | exact resolve eq161761 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161761
  have eq161765 : (σ y) = (M.op (σ x) (M.op (M.op y (M.op x (M.op x y))) (σ x))) ∨ x = y := by
    first
    | exact superpose eq10564 eq161763
    | exact resolve eq161763 eq10564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10564 eq161763
  have eq161767 : (σ y) = (M.op (σ x) (M.op (M.op y (M.op x (M.op x y))) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq161765
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq161765
    | exact resolve eq161765 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161765
  have eq195919 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq161767 eq9421
    | exact resolve eq9421 eq161767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9421 eq161767
  have eq195970 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq195919
    | exact resolve eq195919 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195919
  have eq196053 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq195970 eq27
    | exact resolve eq27 eq195970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195970
  have eq196183 : x = y := by
    first
    | (have r₁ := eq196053
       have r₂ := eq158293
       grind)
    | exact resolve eq196053 eq158293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158293 eq196053
  have eq196184 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq196183
       grind)
    | exact superpose eq196183 eq18
    | exact resolve eq18 eq196183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq196185 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq196183
       grind)
    | exact superpose eq196183 eq24
    | exact resolve eq24 eq196183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq196183
  have eq210105 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq196185
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq196185
    | exact resolve eq196185 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196185
  have eq210812 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq210105 eq26
    | exact resolve eq26 eq210105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq210105
  have eq213993 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq284 x
       have i₂ := eq196184
       grind)
    | exact superpose eq196184 eq284
    | exact resolve eq284 eq196184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284 eq196184
  have eq215239 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq213993
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq213993
    | exact resolve eq213993 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq213993
  have eq216799 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq210812 eq215239
    | exact resolve eq215239 eq210812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210812 eq215239
  have eq217910 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq216799
    | exact resolve eq216799 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq216799
  have eq218600 : False := by grind
  exact eq218600
