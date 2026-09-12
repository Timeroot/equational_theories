import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2659`: `x = ((x ◇ y) ◇ (x ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pxy_x_pxy_Equation2659 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2659 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2659.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X0)) X0) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq62 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq62 (σ X0)
       grind)
    | exact superpose eq62 eq15
    | exact resolve eq15 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq65
    | exact resolve eq65 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq91 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq9
    | exact resolve eq9 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq91 X0
       have i₂ := eq76 (M.op X0 X0)
       grind)
    | exact superpose eq76 eq91
    | exact resolve eq91 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq530 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq547 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq530 X0 X1
       have i₂ := eq76 X1
       grind)
    | exact superpose eq76 eq530
    | (have j0 := eq530 X0 X1
       grind)
    | exact resolve eq530 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq602 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq547 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq547
    | exact resolve eq547 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq644 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq602 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq602
    | (have j0 := eq602 X0 X1
       grind)
    | exact resolve eq602 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq651 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq644 X0 X1
       have j1 := eq92 X1 X0
       grind)
    | (have r₁ := eq644 X1 X0
       have r₂ := eq92 X0 X1
       grind)
    | exact resolve eq644 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq644
  have eq655 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq651 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq651
    | exact resolve eq651 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq656 : ∀ X0 X1 X2 : G, (M.op X2 (k X0 (σ X1))) = X2 ∨ (k X2 (k X0 (σ X1))) = (M.op X2 (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq651 X0 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq651
    | exact resolve eq651 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq665 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq651 X0 X1
       grind)
    | exact superpose eq651 eq22
    | (have j1 := eq651 X0 X1
       grind)
    | exact resolve eq22 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq666 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq651 (σ X0) X1
       grind)
    | exact superpose eq651 eq15
    | (have j1 := eq651 (σ X0) X1
       grind)
    | exact resolve eq15 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq695 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq655 (τ X1) X0
       grind)
    | exact superpose eq655 eq18
    | (have j1 := eq655 (τ X1) X0
       grind)
    | exact resolve eq18 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq655
  have eq719 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ (M.op (M.op X0 X0) (M.op X0 X0)))) X0) ∨ (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq665 (σ (M.op (M.op X0 X0) (M.op X0 X0))) X0
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq665
    | exact resolve eq665 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq742 : ∀ X0 : G, (τ (σ X0)) = (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) ∨ (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq719 X0
       have i₂ := eq10 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq10 eq719
    | (have j0 := eq719 X0
       grind)
    | exact resolve eq719 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq753 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq742 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq742
    | (have j0 := eq742 X0
       grind)
    | exact resolve eq742 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq799 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq695 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq695
    | exact resolve eq695 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq874 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq799 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq799
    | (have j0 := eq799 X0 X1
       grind)
    | exact resolve eq799 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799
  have eq1148 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq666 x y
       grind)
    | exact superpose eq666 eq16
    | (have j1 := eq666 x y
       grind)
    | exact resolve eq16 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1169 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq666 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq1325 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1148
       have i₂ := eq874 y x
       grind)
    | exact superpose eq874 eq1148
    | (have j1 := eq874 (σ y) (σ x)
       grind)
    | (have r₁ := eq1148
       have r₂ := eq874 y x
       grind)
    | exact resolve eq1148 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148
  have eq1326 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1325
  have eq10532 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (k X1 (σ X2)) (k X1 (σ X2))) = (M.op (k X1 (σ X2)) X0) ∨ (k X0 (k X1 (σ X2))) = X0 ∨ (k X0 (k X1 (σ X2))) = (M.op X0 (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (k X1 (σ X2))
       have i₂ := eq656 X1 X2 X0
       grind)
    | exact superpose eq656 eq13
    | (have j0 := eq13 X0 (k X1 (σ X2))
       have j1 := eq656 X1 X2 X0
       grind)
    | (have r₁ := eq13 X2 (k X0 (σ X1))
       have r₂ := eq656 X0 X1 X2
       grind)
    | exact resolve eq13 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq10547 : ∀ X0 X1 X2 : G, (M.op (k X1 (σ X2)) (k X1 (σ X2))) = (M.op (k X1 (σ X2)) X0) ∨ (k X0 (k X1 (σ X2))) = X0 ∨ (k X0 (k X1 (σ X2))) = (M.op X0 (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq10532 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10532
  have eq10552 : ∀ X0 X1 X2 : G, (k X0 (k X1 (σ X2))) = (M.op X0 (k X1 (σ X2))) ∨ (k X0 (k X1 (σ X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq10547 X0 X1 X2
       have j1 := eq12 X0 (k X1 (σ X2))
       grind)
    | (have r₁ := eq10547 (k X1 (σ X2)) X1 X2
       have r₂ := eq12 (k X1 (σ X2)) (k X1 (σ X2))
       grind)
    | (have r₁ := eq10547 X0 X1 X2
       have r₂ := eq12 X0 (k X1 (σ X2))
       grind)
    | exact resolve eq10547 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10547
  have eq11586 : ∀ X0 X1 X2 : G, (M.op X0 (k X1 (σ X2))) ≠ X0 ∨ (k X0 (k X1 (σ X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq10552 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10552
  have eq11626 : ∀ X0 X1 X2 : G, (M.op X1 (k X2 X0)) ≠ X1 ∨ (k X1 (k X2 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11586 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11586
    | exact resolve eq11586 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11648 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (σ X0))) ≠ X1 ∨ (k X1 (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11586 X0 (σ x) x
       have i₂ := eq62 (σ x)
       grind)
    | exact superpose eq62 eq11586
    | exact resolve eq11586 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11586
  have eq11677 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) ≠ X1 ∨ (k X1 (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11648 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq11648
    | (have j0 := eq11648 X0 X1
       grind)
    | exact resolve eq11648 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11648
  have eq11678 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) ≠ X1 ∨ (k X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11677 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq11677
    | (have j0 := eq11677 X0 X1
       grind)
    | exact resolve eq11677 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11677
  have eq11772 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) ≠ X1 ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11626 X0 X1 X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq11626
    | exact resolve eq11626 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq18293 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq95 X0
       have i₂ := eq753 X0
       grind)
    | exact superpose eq753 eq95
    | (have j1 := eq753 X0
       grind)
    | exact resolve eq95 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq753
  have eq18392 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq18293 X0
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq18293
    | (have j0 := eq18293 X0
       grind)
    | exact resolve eq18293 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18293
  have eq18571 : ∀ X0 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq18392 X0
       grind)
    | exact superpose eq18392 eq10
    | (have j1 := eq18392 X0
       grind)
    | exact resolve eq10 eq18392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18392
  have eq18656 : ∀ X0 : G, (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq18571 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18571
    | (have j0 := eq18571 X0
       grind)
    | exact resolve eq18571 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18571
  have eq18734 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11626 X0 X1 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq18656 X0
       grind)
    | exact superpose eq18656 eq11626
    | (have j1 := eq18656 X0
       grind)
    | (have r₁ := eq11626 X0 (k x X0) x
       have r₂ := eq18656 (k x X0)
       grind)
    | exact resolve eq11626 eq18656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11626 eq18656
  have eq19067 : x ≠ x ∨ x = (k x y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18734 y x
       have i₂ := eq1326
       grind)
    | exact superpose eq1326 eq18734
    | (have j0 := eq18734 y x
       grind)
    | (have r₁ := eq18734 y x
       have r₂ := eq1326
       grind)
    | (have r₁ := eq18734 (σ y) (σ x)
       have r₂ := eq1326
       grind)
    | exact resolve eq18734 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19068 : x = (k x y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19067
  have eq20263 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1169 x y
       have i₂ := eq19068
       grind)
    | exact superpose eq19068 eq1169
    | (have j0 := eq1169 x y
       grind)
    | exact resolve eq1169 eq19068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19068
  have eq20294 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq20263
  have eq20295 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20294
  have eq20323 : ∀ X0 : G, (M.op X0 y) ≠ X0 ∨ (k X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11772 y x
       have i₂ := eq20295
       grind)
    | exact superpose eq20295 eq11772
    | exact resolve eq11772 eq20295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11772 eq20295
  have eq21212 : x ≠ x ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20323 x
       have i₂ := eq1326
       grind)
    | exact superpose eq1326 eq20323
    | (have j0 := eq20323 x
       grind)
    | (have r₁ := eq20323 x
       have r₂ := eq1326
       grind)
    | exact resolve eq20323 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326 eq20323
  have eq21216 : x ≠ x ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21212
  have eq21217 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21216
  have eq21249 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1169 x y
       have i₂ := eq21217
       grind)
    | exact superpose eq21217 eq1169
    | (have j0 := eq1169 x y
       grind)
    | exact resolve eq1169 eq21217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169 eq21217
  have eq21280 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21249
  have eq21281 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21280
  have eq21292 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21281
       grind)
    | exact superpose eq21281 eq16
    | exact resolve eq16 eq21281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21305 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq18734 (σ y) (σ x)
       have i₂ := eq21281
       grind)
    | exact superpose eq21281 eq18734
    | (have j0 := eq18734 (σ y) (σ x)
       grind)
    | (have r₁ := eq18734 (σ y) (σ x)
       have r₂ := eq21281
       grind)
    | exact resolve eq18734 eq21281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18734
  have eq21310 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq21305
  have eq21319 : (σ x) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq21310
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq21310
    | exact resolve eq21310 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21310
  have eq21335 : (σ x) = (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq21319
       have i₂ := eq76 y
       grind)
    | exact superpose eq76 eq21319
    | exact resolve eq21319 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq21319
  have eq21562 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq874 y x
       have i₂ := eq21335
       grind)
    | exact superpose eq21335 eq874
    | (have j0 := eq874 y x
       grind)
    | exact resolve eq874 eq21335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21335
  have eq21662 : x = (M.op x y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq21562
       have r₂ := eq21292
       grind)
    | exact resolve eq21562 eq21292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21562
  have eq21725 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq21292
       have i₂ := eq21662
       grind)
    | exact superpose eq21662 eq21292
    | exact resolve eq21292 eq21662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21662
  have eq21747 : (σ y) = (σ (M.op y y)) := by grind
  clear eq21725
  have eq21759 : ∀ X0 : G, (M.op X0 (σ y)) ≠ X0 ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq11678 y x
       have i₂ := eq21747
       grind)
    | exact superpose eq21747 eq11678
    | exact resolve eq11678 eq21747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11678 eq21747
  have eq22874 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq21759 (σ x)
       have i₂ := eq21281
       grind)
    | exact superpose eq21281 eq21759
    | (have j0 := eq21759 (σ x)
       grind)
    | (have r₁ := eq21759 (σ x)
       have r₂ := eq21281
       grind)
    | exact resolve eq21759 eq21281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21281 eq21759
  have eq22903 : (σ x) = (k (σ x) (σ y)) := by grind
  clear eq22874
  have eq22926 : (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq22903
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq22903
    | exact resolve eq22903 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22903
  have eq22962 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq874 y x
       have i₂ := eq22926
       grind)
    | exact superpose eq22926 eq874
    | (have j0 := eq874 y x
       grind)
    | exact resolve eq874 eq22926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874 eq22926
  have eq23062 : x = (M.op x y) := by
    first
    | (have r₁ := eq22962
       have r₂ := eq21292
       grind)
    | exact resolve eq22962 eq21292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22962
  have eq23125 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq21292
       have i₂ := eq23062
       grind)
    | exact superpose eq23062 eq21292
    | exact resolve eq21292 eq23062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21292 eq23062
  have eq23148 : False := by grind
  exact eq23148

/-- `Equation2659`: `x = ((x ◇ y) ◇ (x ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyy_pxy_pyy_pxy_Equation2659 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2659 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2659.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq31 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq32 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq32 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq32 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq37 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq37 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq37 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq39 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq44
    | (have j0 := eq44 X0 X1
       grind)
    | exact resolve eq44 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq45
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq50 X0 X1
       grind)
    | (have r₁ := eq51 X0 X1
       have r₂ := eq50 X0 X1
       grind)
    | exact resolve eq51 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq51
  have eq96 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq100 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq96 X0 X1
       have j1 := eq53 X0 X1
       grind)
    | (have r₁ := eq96 X0 X1
       have r₂ := eq53 X0 X1
       grind)
    | (have r₁ := eq96 X0 X0
       have r₂ := eq53 X0 X0
       grind)
    | exact resolve eq96 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq96
  have eq221 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq100 (σ X0) (σ X1)
       grind)
    | exact superpose eq100 eq15
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq221 X0 X1
       have i₂ := eq100 X0 X1
       grind)
    | exact superpose eq100 eq221
    | exact resolve eq221 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq221
  have eq230 : False := by grind
  exact eq230

/-- `Equation2659`: `x = ((x ◇ y) ◇ (x ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyy_pxy_Equation2659 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2659 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2659.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq21 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq21 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq26 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq29 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq26 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq39 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) := by
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
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq36 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq36 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq38 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq39 X1 X0
       grind)
    | (have r₁ := eq45 X1 X0
       have r₂ := eq39 X0 X1
       grind)
    | exact resolve eq45 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq45
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq50
    | (have j0 := eq50 X0 X1
       grind)
    | exact resolve eq50 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq50
  have eq101 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq105 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq101 X0 X1
       have j1 := eq52 X0 X1
       grind)
    | (have r₁ := eq101 X0 X1
       have r₂ := eq52 X0 X1
       grind)
    | (have r₁ := eq101 X0 X0
       have r₂ := eq52 X0 X0
       grind)
    | exact resolve eq101 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq101
  have eq243 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq105 (σ X0) (σ X1)
       grind)
    | exact superpose eq105 eq15
    | exact resolve eq15 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq243 X0 X1
       have i₂ := eq105 X0 X1
       grind)
    | exact superpose eq105 eq243
    | exact resolve eq243 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq243
  have eq253 : False := by grind
  exact eq253

/-- `Equation2659`: `x = ((x ◇ y) ◇ (x ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation2659 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2659 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2659.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  clear eq18
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
  have eq149 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
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
  have eq150 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq707 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq150 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq736 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (τ X1)
       have i₂ := eq149 X0 X1
       grind)
    | exact superpose eq149 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq149 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X1)
       have r₂ := eq149 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) X1
       have r₂ := eq149 (M.op (τ X1) X1) X1
       grind)
    | exact resolve eq13 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq754 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq736 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq755 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq754 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq2275 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq755 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq755
    | exact resolve eq755 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq2330 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2275 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2275
    | (have j0 := eq2275 X0 X1
       grind)
    | exact resolve eq2275 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2275
  have eq2372 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq2330 X1 X0
       grind)
    | exact superpose eq2330 eq10
    | (have j1 := eq2330 X1 X0
       grind)
    | exact resolve eq10 eq2330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2416 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2372 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq2372
    | (have j0 := eq2372 X0 X1
       grind)
    | exact resolve eq2372 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2372
  have eq2431 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq2416 X0 (σ X1)
       grind)
    | exact superpose eq2416 eq28
    | (have j1 := eq2416 X0 (σ X1)
       grind)
    | exact resolve eq28 eq2416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2416
  have eq4250 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X1)
       have i₂ := eq2431 (σ X0) X1
       grind)
    | exact superpose eq2431 eq37
    | (have j1 := eq2431 (σ X0) X1
       grind)
    | exact resolve eq37 eq2431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2431
  have eq4315 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4250 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4250
    | (have j0 := eq4250 X0 X1
       grind)
    | exact resolve eq4250 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4250
  have eq4347 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4315 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4315
    | (have j0 := eq4315 X0 X1
       grind)
    | exact resolve eq4315 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4315
  have eq4357 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4347 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4347
    | (have j0 := eq4347 X0 X1
       grind)
    | exact resolve eq4347 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4347
  have eq4563 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq4357 X0 X1
       grind)
    | exact superpose eq4357 eq11
    | (have j1 := eq4357 X0 X1
       grind)
    | exact resolve eq11 eq4357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4357
  have eq5468 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4563 x y
       grind)
    | exact superpose eq4563 eq16
    | (have j1 := eq4563 x y
       grind)
    | exact resolve eq16 eq4563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4563
  have eq5501 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5468
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq5468
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq5468
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5468
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5468 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5502 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq5468
       have i₂ := eq2330 y x
       grind)
    | exact superpose eq2330 eq5468
    | (have j1 := eq2330 y x
       grind)
    | (have r₁ := eq5468
       have r₂ := eq2330 y x
       grind)
    | (have r₁ := eq5468
       have r₂ := eq2330 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5468
       have r₂ := eq2330 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5468 eq2330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2330 eq5468
  have eq5505 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5502
  have eq5506 : x = y ∨ (σ x) = (σ y) ∨ x = (k x y) := by grind
  clear eq5505
  have eq5507 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5501
  have eq5508 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq5507
  have eq5512 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5506
       grind)
    | exact superpose eq5506 eq16
    | exact resolve eq16 eq5506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5506
  have eq5513 : x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5512
       have r₂ := eq22 x
       grind)
    | exact resolve eq5512 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5512
  have eq5517 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq707 x y
       have i₂ := eq5513
       grind)
    | exact superpose eq5513 eq707
    | (have j0 := eq707 x y
       grind)
    | exact resolve eq707 eq5513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707 eq5513
  have eq5524 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5517
  have eq5525 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5524
  have eq5529 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5508
       grind)
    | exact superpose eq5508 eq16
    | exact resolve eq16 eq5508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5508
  have eq5530 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5529
       have r₂ := eq22 x
       grind)
    | exact resolve eq5529 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5529
  have eq5539 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5525
       grind)
    | exact superpose eq5525 eq16
    | exact resolve eq16 eq5525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5525
  have eq5560 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5539
       have i₂ := eq5530
       grind)
    | exact superpose eq5530 eq5539
    | exact resolve eq5539 eq5530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5530 eq5539
  have eq5561 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq5560
  have eq5562 : (σ x) = (σ y) := by grind
  clear eq5561
  have eq5563 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5562
       grind)
    | exact superpose eq5562 eq16
    | exact resolve eq16 eq5562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5564 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5562
       grind)
    | exact superpose eq5562 eq10
    | exact resolve eq10 eq5562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5562
  have eq5619 : x = y := by
    first
    | (have i₁ := eq5564
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5564
    | exact resolve eq5564 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5564
  have eq5620 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5563
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5563
    | exact resolve eq5563 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5563
  have eq5621 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5620
       have i₂ := eq5619
       grind)
    | exact superpose eq5619 eq5620
    | exact resolve eq5620 eq5619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5619 eq5620
  have eq5622 : False := by grind
  exact eq5622

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,Y) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pyy_pyy_pxy_Equation2666 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X0 := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq21
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
  have eq45 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq47 : (σ (k x (k x x))) = (k (σ x) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq36 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq36
    | exact resolve eq36 eq44
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
  have eq51 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X3 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X1 X1) = (k (M.op (M.op X0 X1) (M.op X0 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X0 X1) (M.op X0 X2)) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X0 X1) (M.op X0 X2)) X1
       grind)
    | (have r₁ := eq13 (M.op (M.op X0 X0) (M.op X0 X2)) X0
       have r₂ := eq14 X0 X0 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq78 : ∀ X1 : G, (M.op X1 X1) = (k (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq88 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq118 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq103
  have eq120 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq105
    | exact resolve eq105 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq122 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq120
    | exact resolve eq120 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq123 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq132 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq133 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq162 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq164 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq133
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq133
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq133 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq133 eq16
    | exact resolve eq16 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq164
  have eq190 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq42
    | (have j1 := eq11 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq42 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq210 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq51 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 y
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ y)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq566 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x X0)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) X2)) y) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq567 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) X2)) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq583 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X1 X2 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq929 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x x) y) := by
    intro X0
    first
    | (have i₁ := eq583 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq583
    | (have j0 := eq583 x y X0
       grind)
    | exact resolve eq583 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq930 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq583
    | (have j0 := eq583 (σ x) (σ y) X0
       grind)
    | exact resolve eq583 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq942 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq583 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq583
    | (have j0 := eq583 x X0 y
       grind)
    | exact resolve eq583 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq943 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq583
    | (have j0 := eq583 (σ x) X0 (σ y)
       grind)
    | exact resolve eq583 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq947 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq583 X0 X1 x
       grind)
    | exact superpose eq583 eq14
    | exact resolve eq14 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq948 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq477 X0 x
       have i₂ := eq583 X0 X0 x
       grind)
    | exact superpose eq583 eq477
    | exact resolve eq477 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq1014 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq947 X0 (M.op X0 X1)
       have i₂ := eq583 X0 X0 X1
       grind)
    | exact superpose eq583 eq947
    | exact resolve eq947 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1019 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 X1 X1 X0
       have i₂ := eq947 (M.op X0 X1) X0
       grind)
    | exact superpose eq947 eq56
    | exact resolve eq56 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1024 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X1
       have i₂ := eq947 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq947 eq14
    | exact resolve eq14 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1041 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1019 X0 X1
       have i₂ := eq583 X0 X1 X1
       grind)
    | exact superpose eq583 eq1019
    | exact resolve eq1019 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019
  have eq1132 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq942 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq942
    | (have j0 := eq942 y
       grind)
    | exact resolve eq942 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq1173 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1132
       have i₂ := eq929 X0
       grind)
    | exact superpose eq929 eq1132
    | exact resolve eq1132 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1225 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq27 eq943
    | (have j0 := eq943 (σ y)
       grind)
    | exact resolve eq943 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1266 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq930 eq1225
    | exact resolve eq1225 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1321 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq948 (M.op X0 X0)
       have i₂ := eq947 X0 (M.op X0 X0)
       grind)
    | exact superpose eq947 eq948
    | exact resolve eq948 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq1327 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1321 X0
       have i₂ := eq583 X0 X0 X0
       grind)
    | exact superpose eq583 eq1321
    | exact resolve eq1321 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321
  have eq1343 : (M.op x x) = (M.op (M.op (M.op (M.op x x) (M.op x x)) (M.op x x)) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1014 (M.op x x) y
       have i₂ := eq1132
       grind)
    | exact superpose eq1132 eq1014
    | exact resolve eq1014 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1347 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op x y))) x) := by
    first
    | exact superpose eq210 eq1014
    | exact resolve eq1014 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1349 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1225 eq1014
    | exact resolve eq1014 eq1225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1353 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ x)) := by
    first
    | exact superpose eq214 eq1014
    | exact resolve eq1014 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1381 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq1353
       have i₂ := eq947 sF4 (M.op sF4 sF4)
       grind)
    | exact superpose eq947 eq1353
    | exact resolve eq1353 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1353
  have eq1385 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1349
       have i₂ := eq947 sF2 (M.op sF2 sF2)
       grind)
    | exact superpose eq947 eq1349
    | exact resolve eq1349 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1349
  have eq1387 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq1347
       have i₂ := eq947 sF0 (M.op sF0 sF0)
       grind)
    | exact superpose eq947 eq1347
    | exact resolve eq1347 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1347
  have eq1391 : (M.op x x) = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1343
       have i₂ := eq947 x (M.op x x)
       grind)
    | exact superpose eq947 eq1343
    | exact resolve eq1343 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947 eq1343
  have eq1423 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1381 eq214
    | exact resolve eq214 eq1381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1432 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1381 eq583
    | exact resolve eq583 eq1381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1443 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq1432 x
       have i₂ := eq583 sF4 sF2 x
       grind)
    | exact superpose eq583 eq1432
    | exact resolve eq1432 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1432
  have eq1448 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) := by
    first
    | exact superpose eq1381 eq1443
    | exact resolve eq1443 eq1381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1443
  have eq1452 : x = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq1387 eq210
    | exact resolve eq210 eq1387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq1461 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1387 eq583
    | exact resolve eq583 eq1387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1472 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) x) := by
    first
    | (have i₁ := eq1461 x
       have i₂ := eq583 sF0 x x
       grind)
    | exact superpose eq583 eq1461
    | exact resolve eq1461 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1461
  have eq1477 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) x) x) := by
    first
    | exact superpose eq1387 eq1472
    | exact resolve eq1472 eq1387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1472
  have eq1605 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq1381 eq1385
    | exact resolve eq1385 eq1381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1385
  have eq1606 : (M.op x x) = (M.op x (M.op (M.op x y) x)) := by
    first
    | exact superpose eq1387 eq1391
    | exact resolve eq1391 eq1387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1391
  have eq2204 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1041 (M.op X0 X1) X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq1041
    | exact resolve eq1041 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2208 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq214 eq1041
    | exact resolve eq1041 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq2212 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1041 (M.op (M.op X0 X0) X0) (M.op X0 X1)
       have i₂ := eq1014 X0 X1
       grind)
    | exact superpose eq1014 eq1041
    | exact resolve eq1041 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2290 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2212 X0 X1
       have i₂ := eq1024 X0 X0
       grind)
    | exact superpose eq1024 eq2212
    | exact resolve eq2212 eq1024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024 eq2212
  have eq2297 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2290 X0 X1
       have i₂ := eq583 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq583 eq2290
    | exact resolve eq2290 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2290
  have eq2299 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2297 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq2297
    | exact resolve eq2297 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2297
  have eq3818 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) y) := by
    intro X1
    first
    | exact superpose eq1173 eq213
    | (have j0 := eq213 y X1
       grind)
    | exact resolve eq213 eq1173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq3819 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) y) := by
    intro X1
    first
    | exact superpose eq1387 eq3818
    | exact resolve eq3818 eq1387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3818
  have eq3843 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2204 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq2204 X0 X1
       grind)
    | exact superpose eq2204 eq2204
    | exact resolve eq2204 eq2204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3868 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq2208 eq2204
    | exact resolve eq2204 eq2208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2208
  have eq3904 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2299 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq2204 X0 X1
       grind)
    | exact superpose eq2204 eq2299
    | exact resolve eq2299 eq2204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3905 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3904 X0 X1
       have i₂ := eq583 (M.op X0 X1) X1 X1
       grind)
    | exact superpose eq583 eq3904
    | exact resolve eq3904 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3904
  have eq3926 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq3868
       have i₂ := eq1041 sF2 sF4
       grind)
    | exact superpose eq1041 eq3868
    | exact resolve eq3868 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3868
  have eq3946 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3843 X0 X1
       have i₂ := eq1041 X0 (M.op X0 X1)
       grind)
    | exact superpose eq1041 eq3843
    | exact resolve eq3843 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3843
  have eq3960 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3905 X0 X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq3905
    | exact resolve eq3905 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3905
  have eq3973 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq943 eq3926
    | exact resolve eq3926 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943 eq3926
  have eq3983 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3946 X0 X1
       have i₂ := eq583 X0 X0 X1
       grind)
    | exact superpose eq583 eq3946
    | exact resolve eq3946 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3946
  have eq4069 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op (M.op X0 X1) X1) X0
       have i₂ := eq3960 X0 X1
       grind)
    | exact superpose eq3960 eq13
    | (have j0 := eq13 (M.op (M.op X0 X1) X1) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op X0 X1) X1) X0
       have r₂ := eq3960 X0 X1
       grind)
    | exact resolve eq13 eq3960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4083 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq4069 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4069
  have eq4197 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op (M.op (M.op (M.op x y) x) y) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq3819 eq2204
    | exact resolve eq2204 eq3819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3819
  have eq4203 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op x (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq1452 eq4197
    | exact resolve eq4197 eq1452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452 eq4197
  have eq4211 : ∀ X0 : G, (M.op x x) = (M.op x (M.op (M.op (M.op x y) x) X0)) := by
    intro X0
    first
    | exact superpose eq1606 eq4203
    | exact resolve eq4203 eq1606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1606 eq4203
  have eq4449 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1266 eq217
    | (have j0 := eq217 (σ y) X1
       grind)
    | exact resolve eq217 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq4450 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1381 eq4449
    | exact resolve eq4449 eq1381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4449
  have eq4473 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq4450 eq2204
    | exact resolve eq2204 eq4450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4450
  have eq4479 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq1423 eq4473
    | exact resolve eq4473 eq1423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1423 eq4473
  have eq4487 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq1605 eq4479
    | exact resolve eq4479 eq1605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1605 eq4479
  have eq6407 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq162 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq162
    | (have j0 := eq162 x
       grind)
    | exact resolve eq162 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq6427 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6407
  have eq6432 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6427
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq6427
    | exact resolve eq6427 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6427
  have eq6440 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq6432
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq6432 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6432
  have eq6446 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq6440 eq50
    | exact resolve eq50 eq6440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq6543 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq190 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq190
    | (have j0 := eq190 y
       grind)
    | exact resolve eq190 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6545 : ∀ X0 : G, (σ y) ≠ (σ (k X0 y)) ∨ (k (σ X0) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq190 eq13
    | (have j0 := eq13 (σ X0) (σ y)
       have j1 := eq190 X0
       grind)
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq190 y
       grind)
    | (have r₁ := eq13 (σ X0) (σ y)
       have r₂ := eq190 X0
       grind)
    | exact resolve eq13 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq6562 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6543
  have eq6564 : ∀ X0 : G, (σ y) ≠ (σ (k X0 y)) ∨ (k (σ X0) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq6545 X0
       have j1 := eq13 (σ X0) (σ y)
       grind)
    | (have r₁ := eq6545 y
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq6545 X0
       have r₂ := eq13 (σ X0) (σ y)
       grind)
    | exact resolve eq6545 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6545
  have eq6566 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6562
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq6562
    | exact resolve eq6562 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq6562
  have eq6577 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (σ (k X0 y)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq41 eq6564
    | (have j0 := eq6564 X0
       grind)
    | exact resolve eq6564 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq6564
  have eq6578 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq6566
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq6566 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6566
  have eq6603 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq6578 eq88
    | exact resolve eq88 eq6578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq6578
  have eq6690 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq208
    | (have j0 := eq208 (M.op x y)
       grind)
    | exact resolve eq208 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq6708 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq6690
  have eq6711 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq133 eq6708
    | exact resolve eq6708 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq6708
  have eq6727 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq6711
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6711 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6711
  have eq6761 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq6727 eq167
    | exact resolve eq167 eq6727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq6813 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3983 X0 X2
       have i₂ := eq3983 X0 X1
       grind)
    | (have i₁ := eq3983 X1 X1
       have i₂ := eq3983 X1 X1
       grind)
    | exact superpose eq3983 eq3983
    | exact resolve eq3983 eq3983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6818 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | exact superpose eq3973 eq3983
    | exact resolve eq3983 eq3973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3973 eq3983
  have eq9339 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq1173 eq566
    | (have j0 := eq566 y X1 X2
       grind)
    | exact resolve eq566 eq1173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566 eq1173
  have eq9340 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) x) X1)) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq1387 eq9339
    | exact resolve eq9339 eq1387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9339
  have eq9341 : ∀ X2 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x x) X2)) y) := by
    intro X2
    first
    | exact superpose eq4211 eq9340
    | exact resolve eq9340 eq4211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4211 eq9340
  have eq9346 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x y) (M.op x X0))) y) := by
    intro X0
    first
    | (have i₁ := eq9341 y
       have i₂ := eq929 X0
       grind)
    | exact superpose eq929 eq9341
    | exact resolve eq9341 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929 eq9341
  have eq9383 : (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) x) y) := by
    first
    | (have i₁ := eq9346 x
       have i₂ := eq583 sF0 x (M.op x x)
       grind)
    | exact superpose eq583 eq9346
    | exact resolve eq9346 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9346
  have eq9398 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) y) := by
    first
    | (have i₁ := eq9383
       have i₂ := eq1041 sF0 x
       grind)
    | exact superpose eq1041 eq9383
    | exact resolve eq9383 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9383
  have eq9410 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) x) y) := by
    first
    | exact superpose eq1477 eq9398
    | exact resolve eq9398 eq1477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477 eq9398
  have eq9463 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq1266 eq567
    | (have j0 := eq567 (σ y) X1 X2
       grind)
    | exact resolve eq567 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567 eq1266
  have eq9464 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq1381 eq9463
    | exact resolve eq9463 eq1381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381 eq9463
  have eq9465 : ∀ X2 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ x)) X2)) (σ y)) := by
    intro X2
    first
    | exact superpose eq4487 eq9464
    | exact resolve eq9464 eq4487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4487 eq9464
  have eq9471 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) (σ y)) := by
    intro X0
    first
    | exact superpose eq930 eq9465
    | exact resolve eq9465 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930 eq9465
  have eq9508 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq9471 x
       have i₂ := eq583 sF4 sF2 (M.op sF2 x)
       grind)
    | exact superpose eq583 eq9471
    | exact resolve eq9471 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583 eq9471
  have eq9523 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq9508
       have i₂ := eq1041 sF4 sF2
       grind)
    | exact superpose eq1041 eq9508
    | exact resolve eq9508 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9508
  have eq9535 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1448 eq9523
    | exact resolve eq9523 eq1448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448 eq9523
  have eq12122 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) X0) X0) y) := by
    intro X0
    first
    | (have i₁ := eq9410
       have i₂ := eq6813 sF0 x x
       grind)
    | (have i₁ := eq9410
       have i₂ := eq6813 sF0 x x
       grind)
    | exact superpose eq6813 eq9410
    | exact resolve eq9410 eq6813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9410
  have eq12144 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9535
       have i₂ := eq6813 sF4 sF2 x
       grind)
    | (have i₁ := eq9535
       have i₂ := eq6813 sF4 x sF2
       grind)
    | exact superpose eq6813 eq9535
    | exact resolve eq9535 eq6813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6813 eq9535
  have eq35245 : (σ (M.op x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq6440 eq118
    | exact resolve eq118 eq6440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq35315 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq123 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq35324 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq35315
    | exact resolve eq35315 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35315
  have eq35331 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq35324
       have r₂ := eq28
       grind)
    | exact resolve eq35324 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35324
  have eq35333 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq35331
    | exact resolve eq35331 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35331
  have eq35335 : (τ (σ x)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq35333 eq6603
    | exact resolve eq6603 eq35333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6603 eq35333
  have eq35408 : x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq35335
    | exact resolve eq35335 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq35335
  have eq36631 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1387 eq172
    | exact resolve eq172 eq1387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq36632 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq6727 eq36631
    | exact resolve eq36631 eq6727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6727 eq36631
  have eq36633 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1387 eq36632
    | exact resolve eq36632 eq1387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36632
  have eq37202 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq35408
       grind)
    | exact superpose eq35408 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq35408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37218 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq37202
  have eq39229 : y = (k y y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq78 y
       have i₂ := eq37218
       grind)
    | exact superpose eq37218 eq78
    | exact resolve eq78 eq37218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39280 : x ≠ y ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq37218
  have eq40255 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35408
       have i₂ := eq39229
       grind)
    | exact superpose eq39229 eq35408
    | exact resolve eq35408 eq39229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35408 eq39229
  have eq40281 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq40255
  have eq40293 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq40281
       have r₂ := eq39280
       grind)
    | exact resolve eq40281 eq39280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39280 eq40281
  have eq40362 : y = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2204 y y
       have i₂ := eq40293
       grind)
    | exact superpose eq40293 eq2204
    | exact resolve eq2204 eq40293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40367 : x = (k (M.op x y) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4083 y y
       have i₂ := eq40293
       grind)
    | exact superpose eq40293 eq4083
    | exact resolve eq4083 eq40293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4083 eq40293
  have eq40383 : x = (k (M.op x y) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40367
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq40367
    | exact resolve eq40367 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40367
  have eq40387 : y = (M.op (M.op x x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40362
       have i₂ := eq1041 x y
       grind)
    | exact superpose eq1041 eq40362
    | exact resolve eq40362 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041 eq40362
  have eq40400 : y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40387
       have i₂ := eq1132
       grind)
    | exact superpose eq1132 eq40387
    | exact resolve eq40387 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132 eq40387
  have eq40402 : y = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1387 eq40400
    | exact resolve eq40400 eq1387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1387 eq40400
  have eq40787 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40383 eq132
    | exact resolve eq132 eq40383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq40383
  have eq40819 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40787
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq40787
    | exact resolve eq40787 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40787
  have eq46099 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40402 eq36633
    | exact resolve eq36633 eq40402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36633 eq40402
  have eq46164 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq46099
  have eq46179 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq46164
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq46164
    | exact resolve eq46164 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46164
  have eq46193 : (M.op (σ y) (σ (M.op x y))) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46179 eq1327
    | exact resolve eq1327 eq46179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46225 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ (M.op x y))) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46179 eq1014
    | exact resolve eq1014 eq46179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014 eq46179
  have eq47775 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46193 eq40819
    | exact resolve eq40819 eq46193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40819 eq46193
  have eq47785 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq47775
  have eq49149 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq47785 eq46225
    | exact resolve eq46225 eq47785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46225 eq47785
  have eq49175 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq49149
  have eq49186 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq49175
    | exact resolve eq49175 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49175
  have eq49195 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq49186
       have r₂ := eq28
       grind)
    | exact resolve eq49186 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49186
  have eq49260 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ y) X0) X0) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq49195 eq12144
    | exact resolve eq12144 eq49195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12144 eq49195
  have eq49268 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq49260 x
       have i₂ := eq3960 sF3 x
       grind)
    | exact superpose eq3960 eq49260
    | exact resolve eq49260 eq3960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49260
  have eq49519 : (τ (σ y)) = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq49268 eq6446
    | exact resolve eq6446 eq49268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6446 eq49268
  have eq49624 : y = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq49519
    | exact resolve eq49519 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq49519
  have eq50302 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq49624
       grind)
    | exact superpose eq49624 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq49624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50318 : y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq50302
  have eq161581 : y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2299 x x
       have i₂ := eq50318
       grind)
    | exact superpose eq50318 eq2299
    | exact resolve eq2299 eq50318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50318
  have eq161606 : y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq161581
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq161581
    | exact resolve eq161581 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161581
  have eq161607 : x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq161606
  have eq161689 : x = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq78 x
       have i₂ := eq161607
       grind)
    | exact superpose eq161607 eq78
    | exact resolve eq78 eq161607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161886 : x = y ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq49624
       have i₂ := eq161689
       grind)
    | exact superpose eq161689 eq49624
    | exact resolve eq49624 eq161689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49624 eq161689
  have eq161924 : y = (M.op x y) ∨ x = y := by grind
  clear eq161886
  have eq161976 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq161924 eq21
    | exact resolve eq21 eq161924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162156 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op y X0) X0) y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq161924 eq12122
    | exact resolve eq12122 eq161924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12122 eq161924
  have eq162199 : y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq162156 x
       have i₂ := eq3960 y x
       grind)
    | exact superpose eq3960 eq162156
    | exact resolve eq162156 eq3960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3960 eq162156
  have eq162320 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq161976
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq161976
    | exact resolve eq161976 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161976
  have eq175382 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq35245
       have i₂ := eq162199
       grind)
    | exact superpose eq162199 eq35245
    | exact resolve eq35245 eq162199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35245 eq162199
  have eq175490 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq175382
  have eq175514 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq175490
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq175490
    | exact resolve eq175490 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175490
  have eq187468 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq175514 eq2299
    | exact resolve eq2299 eq175514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2299 eq175514
  have eq187485 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq187468
    | exact resolve eq187468 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq187468
  have eq187629 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq187485 eq28
    | exact resolve eq28 eq187485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187485
  have eq187896 : x = y := by
    first
    | (have r₁ := eq187629
       have r₂ := eq162320
       grind)
    | exact resolve eq187629 eq162320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162320 eq187629
  have eq187899 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq187896
       grind)
    | exact superpose eq187896 eq19
    | exact resolve eq19 eq187896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq187900 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq187896
       grind)
    | exact superpose eq187896 eq25
    | exact resolve eq25 eq187896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq188322 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq187900
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq187900
    | exact resolve eq187900 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187900
  have eq189327 : x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq161607
       have i₂ := eq187899
       grind)
    | exact superpose eq187899 eq161607
    | exact resolve eq161607 eq187899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161607
  have eq189470 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq189327
       have i₂ := eq187896
       grind)
    | exact superpose eq187896 eq189327
    | exact resolve eq189327 eq187896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189327
  have eq189471 : x = (M.op x y) := by grind
  clear eq189470
  have eq189526 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq189471 eq21
    | exact resolve eq21 eq189471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189943 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq189526
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq189526
    | exact resolve eq189526 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq189526
  have eq191703 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ x) (σ x)) ∨ (σ y) ≠ (σ (k X0 y)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq188322 eq6577
    | (have j0 := eq6577 X0
       grind)
    | exact resolve eq6577 eq188322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6577
  have eq191704 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) ≠ (σ (k X0 y)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq189943 eq191703
    | (have j0 := eq191703 X0
       grind)
    | exact resolve eq191703 eq189943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191703
  have eq191705 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) ≠ (σ (k X0 y)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq191704 X0
       have i₂ := eq187896
       grind)
    | exact superpose eq187896 eq191704
    | (have j0 := eq191704 X0
       grind)
    | exact resolve eq191704 eq187896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191704
  have eq191706 : ∀ X0 : G, (σ y) ≠ (σ (k X0 x)) ∨ (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq191705 X0
       have i₂ := eq187896
       grind)
    | exact superpose eq187896 eq191705
    | (have j0 := eq191705 X0
       grind)
    | exact resolve eq191705 eq187896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187896 eq191705
  have eq191707 : ∀ X0 : G, (σ x) ≠ (σ (k X0 x)) ∨ (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq188322 eq191706
    | (have j0 := eq191706 X0
       grind)
    | exact resolve eq191706 eq188322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191706
  have eq191708 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k X0 x)) ∨ (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq189943 eq191707
    | (have j0 := eq191707 X0
       grind)
    | exact resolve eq191707 eq189943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191707
  have eq191709 : ∀ X0 : G, (σ X0) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (σ (k X0 x)) ∨ (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq188322 eq191708
    | (have j0 := eq191708 X0
       grind)
    | exact resolve eq191708 eq188322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191708
  have eq191710 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k X0 x)) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq189943 eq191709
    | (have j0 := eq191709 X0
       grind)
    | exact resolve eq191709 eq189943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191709
  have eq191735 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq191710 (M.op x x)
       have i₂ := eq78 x
       grind)
    | exact superpose eq78 eq191710
    | (have j0 := eq191710 (M.op x x)
       grind)
    | exact resolve eq191710 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq191710
  have eq191790 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq191735
  have eq191842 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq191790
       have i₂ := eq187899
       grind)
    | exact superpose eq187899 eq191790
    | exact resolve eq191790 eq187899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191790
  have eq191902 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq191842
       have r₂ := eq21
       grind)
    | exact resolve eq191842 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191842
  have eq191950 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq191902
       have i₂ := eq187899
       grind)
    | exact superpose eq187899 eq191902
    | exact resolve eq191902 eq187899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187899 eq191902
  have eq191990 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq191950
    | exact resolve eq191950 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq191950
  have eq192105 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq191990 eq6761
    | exact resolve eq6761 eq191990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6761
  have eq192211 : (τ (σ (M.op x y))) = (k x x) := by
    first
    | exact superpose eq189471 eq192105
    | exact resolve eq192105 eq189471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192105
  have eq192228 : (M.op x y) = (k x x) := by
    first
    | exact superpose eq31 eq192211
    | exact resolve eq192211 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq192211
  have eq192236 : x = (k x x) := by
    first
    | exact superpose eq189471 eq192228
    | exact resolve eq192228 eq189471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189471 eq192228
  have eq192250 : (σ (k x x)) = (k (σ x) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq47
       have i₂ := eq192236
       grind)
    | exact superpose eq192236 eq47
    | exact resolve eq47 eq192236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq192236
  have eq192336 : (σ (k x x)) = (k (σ x) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq6440 eq192250
    | exact resolve eq192250 eq6440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192250
  have eq192365 : (σ (k x x)) = (M.op (M.op (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq192336
       have i₂ := eq1327 sF2
       grind)
    | exact superpose eq1327 eq192336
    | exact resolve eq192336 eq1327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327 eq192336
  have eq192389 : (σ (k x x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq6818 eq192365
    | exact resolve eq192365 eq6818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6818 eq192365
  have eq192402 : (σ (k x x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq188322 eq192389
    | exact resolve eq192389 eq188322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188322 eq192389
  have eq192410 : (σ (k x x)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq189943 eq192402
    | exact resolve eq192402 eq189943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192402
  have eq192415 : (k (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq192410
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq192410
    | exact resolve eq192410 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq192410
  have eq192419 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq6440 eq192415
    | exact resolve eq192415 eq6440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6440 eq192415
  have eq192423 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq189943 eq192419
    | exact resolve eq192419 eq189943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189943 eq192419
  have eq192425 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq191990 eq192423
    | exact resolve eq192423 eq191990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192423
  have eq192477 : (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq192425 eq2204
    | exact resolve eq2204 eq192425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2204 eq192425
  have eq192502 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq191990 eq192477
    | exact resolve eq192477 eq191990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192477
  have eq192552 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq191990 eq192502
    | exact resolve eq192502 eq191990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191990 eq192502
  have eq192591 : False := by grind
  exact eq192591

/-- `Equation2702`: `x = ((y ◇ x) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pxy_y_pxy_Equation2702 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2702 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2702.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X0 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq61 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op X0 X3)) X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op x X0) (M.op X0 x)) X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = (M.op (M.op (M.op (M.op X1 X0) (M.op X0 X2)) X0) (M.op (M.op X1 X0) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 (M.op (M.op X1 X0) (M.op X0 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X0 (M.op X0 X1)) X0) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 (M.op X0 (M.op X0 X1)) X0
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 X1
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq64
    | exact resolve eq64 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq68 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X0 X1 X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq313 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq314 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq313 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313
  have eq316 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq314 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq314 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq314 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq327 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq316 (σ X0)
       grind)
    | exact superpose eq316 eq15
    | exact resolve eq15 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq327 X0
       have i₂ := eq316 X0
       grind)
    | exact superpose eq316 eq327
    | exact resolve eq327 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316 eq327
  have eq395 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq346 X0
       grind)
    | exact superpose eq346 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq396 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq346 X0
       grind)
    | exact superpose eq346 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq397 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq395 X0 X1
       have j1 := eq396 X0 X1
       grind)
    | (have r₁ := eq395 X0 X1
       have r₂ := eq396 X0 X1
       grind)
    | exact resolve eq395 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395 eq396
  have eq555 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq397 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq397
    | exact resolve eq397 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq568 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq397 X1 (σ X0)
       grind)
    | exact superpose eq397 eq15
    | (have j1 := eq397 X1 (σ X0)
       grind)
    | exact resolve eq15 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq598 : ∀ X0 X1 : G, (M.op (τ X1) X0) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq555 (τ X1) X0
       grind)
    | exact superpose eq555 eq18
    | (have j1 := eq555 (τ X1) X0
       grind)
    | exact resolve eq18 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq859 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq598 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq598
    | exact resolve eq598 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq918 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq859 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq859
    | (have j0 := eq859 X0 X1
       grind)
    | exact resolve eq859 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq1037 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X1) (M.op (M.op X0 X1) (M.op X1 X2))) X1) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X3 (M.op (M.op X0 X1) (M.op X1 X2))
       have i₂ := eq68 X1 X0 X2
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1038 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 X2)) ≠ (M.op (M.op X0 X1) (M.op X1 X2)) ∨ (M.op X1 X1) = X1 ∨ (k (M.op (M.op X0 X1) (M.op X1 X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X0 X1) (M.op X1 X2)) X1
       have i₂ := eq68 X1 X0 X2
       grind)
    | exact superpose eq68 eq13
    | (have j0 := eq13 (M.op (M.op X0 X1) (M.op X1 X2)) X1
       grind)
    | (have r₁ := eq13 (M.op (M.op X1 X0) (M.op X0 X2)) X0
       have r₂ := eq68 X0 X1 X2
       grind)
    | exact resolve eq13 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq1044 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k (M.op (M.op X0 X1) (M.op X1 X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq1038 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038
  have eq1131 : ∀ X0 X1 X2 X3 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (k (M.op (M.op X2 X0) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq1044 X2 X0 X3
       grind)
    | exact superpose eq1044 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq1044 X2 X0 X3
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq1044 X0 X1 X2
       grind)
    | exact resolve eq12 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq1164 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (k X1 X0) ∨ (k (M.op (M.op X2 X0) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1131 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131
  have eq1552 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq568 x y
       grind)
    | exact superpose eq568 eq16
    | (have j1 := eq568 x y
       grind)
    | exact resolve eq16 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq1637 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1552
       have i₂ := eq918 y x
       grind)
    | exact superpose eq918 eq1552
    | (have j1 := eq918 (σ y) (σ x)
       grind)
    | (have r₁ := eq1552
       have r₂ := eq918 y x
       grind)
    | exact resolve eq1552 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1638 : x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq1637
  have eq1644 : y = (M.op (M.op y x) y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq61 y x
       have i₂ := eq1638
       grind)
    | exact superpose eq1638 eq61
    | exact resolve eq61 eq1638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1645 : (M.op y x) = (M.op y (M.op y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq67 y x
       have i₂ := eq1638
       grind)
    | exact superpose eq1638 eq67
    | exact resolve eq67 eq1638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq1654 : y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1644
       have i₂ := eq1638
       grind)
    | exact superpose eq1638 eq1644
    | exact resolve eq1644 eq1638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1644
  have eq1667 : y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq1654
  have eq1927 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X1) ≠ X1 ∨ (k (M.op (M.op X0 X1) (M.op X1 X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq1164 X1 X1 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1164
  have eq1929 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 X1) (M.op X1 X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq1927 X0 X1 X2
       grind)
    | (have r₁ := eq1927 X1 X0 X2
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq1927 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1927
  have eq1937 : ∀ X0 X4 : G, (k (M.op X0 (M.op X0 X4)) X0) = X0 := by
    intro X0 X4
    first
    | (have i₁ := eq1929 (M.op (M.op x X0) (M.op (M.op x X0) (M.op X0 x))) X0 X4
       have i₂ := eq1037 x X0 x x
       grind)
    | exact superpose eq1037 eq1929
    | exact resolve eq1929 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037 eq1929
  have eq2065 : y = (k (M.op y x) y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1937 y x
       have i₂ := eq1645
       grind)
    | exact superpose eq1645 eq1937
    | exact resolve eq1937 eq1645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645
  have eq2083 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (M.op (σ X0) X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op (σ X0) (M.op (σ X0) X1)) X0
       have i₂ := eq1937 (σ X0) X1
       grind)
    | exact superpose eq1937 eq22
    | exact resolve eq22 eq1937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1937
  have eq2091 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) (M.op (σ X0) X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2083 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2083
    | exact resolve eq2083 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2083
  have eq4060 : y = (k x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2065
       have i₂ := eq1638
       grind)
    | exact superpose eq1638 eq2065
    | exact resolve eq2065 eq1638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1638 eq2065
  have eq4071 : y = (k x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq4060
  have eq4076 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1552
       have i₂ := eq4071
       grind)
    | exact superpose eq4071 eq1552
    | exact resolve eq1552 eq4071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552 eq4071
  have eq4083 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq4076
  have eq4358 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq4083
       have i₂ := eq1667
       grind)
    | exact superpose eq1667 eq4083
    | exact resolve eq4083 eq1667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1667 eq4083
  have eq4359 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq4358
  have eq4360 : (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq4359
  have eq4405 : y = (k (τ (M.op (σ y) (σ x))) y) := by
    first
    | (have i₁ := eq2091 y (σ x)
       have i₂ := eq4360
       grind)
    | exact superpose eq4360 eq2091
    | exact resolve eq2091 eq4360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2091
  have eq4415 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq61 (σ y) (σ x)
       have i₂ := eq4360
       grind)
    | exact superpose eq4360 eq61
    | exact resolve eq61 eq4360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4437 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4415
       have i₂ := eq4360
       grind)
    | exact superpose eq4360 eq4415
    | exact resolve eq4415 eq4360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4415
  have eq4440 : y = (k (τ (σ x)) y) := by
    first
    | (have i₁ := eq4405
       have i₂ := eq4360
       grind)
    | exact superpose eq4360 eq4405
    | exact resolve eq4405 eq4360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4360 eq4405
  have eq4448 : y = (k x y) := by
    first
    | (have i₁ := eq4440
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4440
    | exact resolve eq4440 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4440
  have eq4457 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq918 y x
       have i₂ := eq4448
       grind)
    | exact superpose eq4448 eq918
    | (have j0 := eq918 y x
       grind)
    | exact resolve eq918 eq4448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918
  have eq4460 : x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq555 y x
       have i₂ := eq4448
       grind)
    | exact superpose eq4448 eq555
    | (have j0 := eq555 y x
       grind)
    | exact resolve eq555 eq4448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555 eq4448
  have eq4630 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4437
       grind)
    | exact superpose eq4437 eq16
    | exact resolve eq16 eq4437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4437
  have eq5191 : y = (M.op (M.op y x) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq61 y x
       have i₂ := eq4457
       grind)
    | exact superpose eq4457 eq61
    | exact resolve eq61 eq4457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq4457
  have eq5217 : y = (M.op (M.op y x) y) := by
    first
    | (have r₁ := eq5191
       have r₂ := eq4630
       grind)
    | exact resolve eq5191 eq4630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5191
  have eq5235 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5217
       have i₂ := eq4460
       grind)
    | exact superpose eq4460 eq5217
    | exact resolve eq5217 eq4460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4460 eq5217
  have eq5256 : y = (M.op x y) := by grind
  clear eq5235
  have eq5268 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq4630
       have i₂ := eq5256
       grind)
    | exact superpose eq5256 eq4630
    | exact resolve eq4630 eq5256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4630 eq5256
  have eq5288 : False := by grind
  exact eq5288

/-- `Equation2702`: `x = ((y ◇ x) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_pyy_pxy_Equation2702 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2702 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2702.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X0 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op X0 X3)) X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op x X0) (M.op X0 x)) X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = (M.op (M.op (M.op (M.op X1 X0) (M.op X0 X2)) X0) (M.op (M.op X1 X0) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (M.op (M.op X1 X0) (M.op X0 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X0 (M.op X0 X1)) X0) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (M.op X0 (M.op X0 X1)) X0
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq22
    | exact resolve eq22 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq26 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X0 X1 X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq21
    | exact resolve eq21 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq36 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq39 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30
    | exact resolve eq30 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36 (k (τ X0) X1) X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq36
    | exact resolve eq36 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq74 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 (σ X0)) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq36
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq36 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) X0) ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq73 X0 X0
       grind)
    | exact superpose eq73 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq73 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq73 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq73 X0 X1
       grind)
    | exact resolve eq12 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq73 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq120 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq119 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq122 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq117 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq123 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq122 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq122 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq122 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq223 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq120 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq120
    | (have j0 := eq120 (τ X0)
       grind)
    | exact resolve eq120 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq225 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq223 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq223
    | (have j0 := eq223 X0
       grind)
    | exact resolve eq223 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq228 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq225 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq225
    | (have j0 := eq225 X0
       grind)
    | exact resolve eq225 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq278 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq123 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq123
    | (have j0 := eq123 (τ X0) X1
       grind)
    | exact resolve eq123 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq278 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq278
    | (have j0 := eq278 X0 X1
       grind)
    | exact resolve eq278 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq283 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq280 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq280
    | (have j0 := eq280 X0 X1
       grind)
    | exact resolve eq280 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq289 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq283 (τ X0) X1
       have i₂ := eq39 X0 X0
       grind)
    | exact superpose eq39 eq283
    | (have j0 := eq283 (τ X0) X1
       grind)
    | exact resolve eq283 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq665 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (M.op (τ X0) X1))) X0) ∨ (τ X0) = (M.op (τ X0) (M.op (τ X0) (M.op (τ X0) X1))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 (M.op (τ X0) (M.op (τ X0) X1)) X0
       have i₂ := eq19 (τ X0) X1
       grind)
    | exact superpose eq19 eq77
    | (have j0 := eq77 (M.op (τ X0) (M.op (τ X0) X1)) X0
       grind)
    | exact resolve eq77 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq696 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) (M.op (τ X0) X1))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (M.op (τ X0) (M.op (τ X0) X1))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq665 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq665
    | (have j0 := eq665 X0 X1
       grind)
    | exact resolve eq665 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq702 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (M.op (τ X0) X1)) ∨ (k (σ (M.op (τ X0) (M.op (τ X0) X1))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq696 X0 X1
       have i₂ := eq25 (τ X0) X1
       grind)
    | exact superpose eq25 eq696
    | (have j0 := eq696 X0 X1
       grind)
    | exact resolve eq696 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq4509 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq74 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq4510 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq4509 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4509
  have eq4513 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq4510 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4510
    | (have j0 := eq4510 X0
       grind)
    | exact resolve eq4510 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4510
  have eq4525 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4513 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4513
    | exact resolve eq4513 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4513
  have eq4576 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4525 X0
       have i₂ := eq39 X0 X0
       grind)
    | exact superpose eq39 eq4525
    | (have j0 := eq4525 X0
       grind)
    | exact resolve eq4525 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4525
  have eq4707 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq4576 X0
       grind)
    | exact superpose eq4576 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq4576 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq4576 X0
       grind)
    | exact resolve eq12 eq4576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4576
  have eq4754 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq4707 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4707
  have eq4955 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq4754 X0 X1
       grind)
    | exact superpose eq4754 eq11
    | (have j1 := eq4754 X0 X1
       grind)
    | exact resolve eq11 eq4754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4754
  have eq5063 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4955 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4955
    | (have j0 := eq4955 X0 X0
       grind)
    | exact resolve eq4955 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4955
  have eq5125 : ∀ X0 X1 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 X0
       have i₂ := eq5063 (τ X0) X1
       grind)
    | exact superpose eq5063 eq39
    | (have j1 := eq5063 (τ X0) X1
       grind)
    | exact resolve eq39 eq5063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5151 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq5063 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5063
  have eq5152 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq5151 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5151
  have eq5183 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5125 X0 X1
       have i₂ := eq5152 X0
       grind)
    | exact superpose eq5152 eq5125
    | (have j0 := eq5125 X0 X1
       grind)
    | exact resolve eq5125 eq5152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5125
  have eq5525 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq123 X0 X1
       have i₂ := eq5152 X0
       grind)
    | exact superpose eq5152 eq123
    | (have j0 := eq123 X0 X1
       grind)
    | exact resolve eq123 eq5152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq5531 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq289 X0 X1
       have i₂ := eq5152 X0
       grind)
    | exact superpose eq5152 eq289
    | (have j0 := eq289 X0 X1
       grind)
    | exact resolve eq289 eq5152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq5564 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq5152 (σ X0)
       grind)
    | exact superpose eq5152 eq15
    | exact resolve eq15 eq5152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5571 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0 X0
       have i₂ := eq5152 (τ X0)
       grind)
    | exact superpose eq5152 eq39
    | exact resolve eq39 eq5152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq5628 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5571 X0
       have i₂ := eq5152 X0
       grind)
    | exact superpose eq5152 eq5571
    | exact resolve eq5571 eq5152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5571
  have eq5635 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5564 X0
       have i₂ := eq5152 X0
       grind)
    | exact superpose eq5152 eq5564
    | exact resolve eq5564 eq5152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5152 eq5564
  have eq16856 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (σ (M.op (τ X0) (M.op (τ X0) X1))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (τ X0) X1
       have i₂ := eq702 X0 X1
       grind)
    | exact superpose eq702 eq25
    | (have j1 := eq702 X0 X1
       grind)
    | exact resolve eq25 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq702
  have eq16920 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (σ (M.op (τ X0) (M.op (τ X0) X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq16856 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16856
  have eq16975 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) (M.op (τ X0) X1))) X0) = X0 ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16920 X0 X1
       have i₂ := eq5628 X0
       grind)
    | exact superpose eq5628 eq16920
    | (have j0 := eq16920 X0 X1
       grind)
    | exact resolve eq16920 eq5628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5628 eq16920
  have eq17042 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 (M.op X0 X1))) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16975 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16975
    | exact resolve eq16975 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17110 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ (M.op (τ (σ X0)) (M.op (τ (σ X0)) X1)))) X0) ∨ (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 (σ (M.op (τ (σ X0)) (M.op (τ (σ X0)) X1))) X0
       have i₂ := eq16975 (σ X0) X1
       grind)
    | exact superpose eq16975 eq30
    | (have j1 := eq16975 (σ X0) X1
       grind)
    | exact resolve eq30 eq16975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16975
  have eq17167 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (τ (σ X0)) (M.op (τ (σ X0)) X1)) X0) ∨ (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17110 X0 X1
       have i₂ := eq10 (M.op (τ (σ X0)) (M.op (τ (σ X0)) X1))
       grind)
    | exact superpose eq10 eq17110
    | (have j0 := eq17110 X0 X1
       grind)
    | exact resolve eq17110 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17110
  have eq17199 : ∀ X0 X1 : G, (σ X0) = (σ (k (M.op X0 (M.op X0 X1)) X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17042 X0 X1
       have i₂ := eq15 (M.op X0 (M.op X0 X1)) X0
       grind)
    | exact superpose eq15 eq17042
    | (have j0 := eq17042 X0 X1
       grind)
    | exact resolve eq17042 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17042
  have eq17226 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X1)) X0) = X0 ∨ (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17167 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17167
    | (have j0 := eq17167 X0 X1
       grind)
    | exact resolve eq17167 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17167
  have eq17251 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X0 ∨ (σ X0) = (σ (k (M.op X0 (M.op X0 X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17199 X0 X1
       have i₂ := eq5635 X0
       grind)
    | exact superpose eq5635 eq17199
    | (have j0 := eq17199 X0 X1
       grind)
    | exact resolve eq17199 eq5635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17199
  have eq17277 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (k (M.op X0 (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17226 X0 X1
       have i₂ := eq5635 X0
       grind)
    | exact superpose eq5635 eq17226
    | (have j0 := eq17226 X0 X1
       grind)
    | exact resolve eq17226 eq5635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17226
  have eq17291 : ∀ X0 X1 : G, (σ X0) = (σ (k (M.op X0 (M.op X0 X1)) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17251 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq17251
    | (have j0 := eq17251 X0 X1
       grind)
    | exact resolve eq17251 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17251
  have eq17298 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k (M.op X0 (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17277 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq17277
    | (have j0 := eq17277 X0 X1
       grind)
    | exact resolve eq17277 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17277
  have eq17312 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X1)) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17298 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17298
    | (have j0 := eq17298 X0 X1
       grind)
    | exact resolve eq17298 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17298
  have eq17402 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (M.op (σ X0) X1))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 (M.op (σ X0) (M.op (σ X0) X1)) X0
       have i₂ := eq17312 (σ X0) X1
       grind)
    | exact superpose eq17312 eq30
    | (have j1 := eq17312 (σ X0) X1
       grind)
    | exact resolve eq30 eq17312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17312
  have eq17466 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) (M.op (σ X0) X1))) X0) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17402 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17402
    | (have j0 := eq17402 X0 X1
       grind)
    | exact resolve eq17402 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17402
  have eq17545 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (τ (M.op (σ X0) (M.op (σ X0) X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17466 X0 X1
       have i₂ := eq5635 X0
       grind)
    | exact superpose eq5635 eq17466
    | (have j0 := eq17466 X0 X1
       grind)
    | exact resolve eq17466 eq5635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17466
  have eq17790 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (k (M.op (τ X0) (τ (M.op X0 X0))) (τ X0))) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17291 (τ X0) (τ X0)
       have i₂ := eq5183 X0 X1
       grind)
    | exact superpose eq5183 eq17291
    | (have j1 := eq5183 X0 X1
       grind)
    | exact resolve eq17291 eq5183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5183 eq17291
  have eq17954 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (k (M.op (τ X0) (τ (M.op X0 X0))) (τ X0))) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq17790 X0 X1
       have j1 := eq5531 X0 X1
       grind)
    | (have r₁ := eq17790 X0 X1
       have r₂ := eq5531 X0 X1
       grind)
    | exact resolve eq17790 eq5531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5531 eq17790
  have eq18016 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ (M.op X0 X0)))) X0) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17954 X0 X1
       have i₂ := eq18 X0 (M.op (τ X0) (τ (M.op X0 X0)))
       grind)
    | exact superpose eq18 eq17954
    | (have j0 := eq17954 X0 X1
       grind)
    | exact resolve eq17954 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq17954
  have eq18047 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) (τ (M.op X0 X0)))) X0) = X0 ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18016 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18016
    | (have j0 := eq18016 X0 X1
       grind)
    | exact resolve eq18016 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18016
  have eq18924 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k (τ (M.op (σ X0) (M.op (σ X0) X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq17545 X0 X1
       grind)
    | exact superpose eq17545 eq10
    | (have j1 := eq17545 X0 X1
       grind)
    | exact resolve eq10 eq17545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17545
  have eq19037 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) (M.op (σ X0) X1))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18924 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18924
    | (have j0 := eq18924 X0 X1
       grind)
    | exact resolve eq18924 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18924
  have eq19713 : ∀ X0 X1 X2 : G, (k (τ (M.op (σ X1) (M.op (M.op X0 (σ X1)) (M.op (σ X1) X2)))) X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19037 X1 (M.op (M.op X0 (σ X1)) (M.op (σ X1) X2))
       have i₂ := eq26 (σ X1) X0 X2
       grind)
    | exact superpose eq26 eq19037
    | (have j0 := eq19037 X1 X1
       grind)
    | exact resolve eq19037 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19037
  have eq19884 : ∀ X0 X1 X2 : G, (k (τ (M.op (M.op X0 (σ X1)) (M.op (σ X1) X2))) X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19713 X0 X1 X2
       have i₂ := eq26 (σ X1) X0 X2
       grind)
    | exact superpose eq26 eq19713
    | (have j0 := eq19713 X0 X1 X2
       grind)
    | exact resolve eq19713 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq19713
  have eq23510 : ∀ X0 X1 : G, (k (τ (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19884 (σ X0) X0 X1
       have i₂ := eq5635 X0
       grind)
    | exact superpose eq5635 eq19884
    | (have j0 := eq19884 X0 X0 x
       grind)
    | exact resolve eq19884 eq5635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19884
  have eq91626 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ (M.op (τ (σ X0)) (τ (M.op (σ X0) (σ X0)))))) X0) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 (σ (M.op (τ (σ X0)) (τ (M.op (σ X0) (σ X0))))) X0
       have i₂ := eq18047 (σ X0) X1
       grind)
    | exact superpose eq18047 eq30
    | (have j1 := eq18047 (σ X0) X1
       grind)
    | exact resolve eq30 eq18047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18047
  have eq91738 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (τ (σ X0)) (τ (M.op (σ X0) (σ X0)))) X0) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq91626 X0 X1
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (M.op (σ X0) (σ X0))))
       grind)
    | exact superpose eq10 eq91626
    | (have j0 := eq91626 X0 X1
       grind)
    | exact resolve eq91626 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91626
  have eq91848 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (τ (σ X0)) (τ (σ (M.op X0 X0)))) X0) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq91738 X0 X1
       have i₂ := eq5635 X0
       grind)
    | exact superpose eq5635 eq91738
    | (have j0 := eq91738 X0 X1
       grind)
    | exact resolve eq91738 eq5635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91738
  have eq91936 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (τ (σ X0)) (M.op X0 X0)) X0) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq91848 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq91848
    | (have j0 := eq91848 X0 X1
       grind)
    | exact resolve eq91848 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91848
  have eq91995 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X0)) X0) = X0 ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq91936 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq91936
    | (have j0 := eq91936 X0 X1
       grind)
    | exact resolve eq91936 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91936
  have eq92042 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X0)) X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq91995 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq91995
    | (have j0 := eq91995 X0 X1
       grind)
    | exact resolve eq91995 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91995
  have eq92236 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) X0) ≠ X0 ∨ (M.op (M.op X0 (M.op X0 X0)) X0) = (k (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have j0 := eq92042 X0 (M.op X0 (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92042
  have eq92238 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (k (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have j0 := eq92236 X0
       grind)
    | (have r₁ := eq92236 x
       have r₂ := eq19 x x
       grind)
    | exact resolve eq92236 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92236
  have eq92308 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq92238 X0
       have i₂ := eq19 X0 X0
       grind)
    | exact superpose eq19 eq92238
    | exact resolve eq92238 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92238
  have eq93298 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) X0) := by
    intro X0
    first
    | (have i₁ := eq30 (M.op (σ X0) (M.op (σ X0) (σ X0))) X0
       have i₂ := eq92308 (σ X0)
       grind)
    | exact superpose eq92308 eq30
    | exact resolve eq30 eq92308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq93300 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (k (k (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op (σ X0) (M.op (σ X0) (σ X0))) X0 X1
       have i₂ := eq92308 (σ X0)
       grind)
    | exact superpose eq92308 eq50
    | exact resolve eq50 eq92308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq92308
  have eq93404 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (k (k (τ (M.op (σ X0) (σ (M.op X0 X0)))) X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq93300 X0 X1
       have i₂ := eq5635 X0
       grind)
    | exact superpose eq5635 eq93300
    | exact resolve eq93300 eq5635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93300
  have eq93406 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ (M.op X0 X0)))) X0) := by
    intro X0
    first
    | (have i₁ := eq93298 X0
       have i₂ := eq5635 X0
       grind)
    | exact superpose eq5635 eq93298
    | exact resolve eq93298 eq5635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93298
  have eq93486 : ∀ X0 X1 : G, (k X0 (τ X1)) = (k (k (τ (M.op (σ X0) (σ (M.op X0 X0)))) X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq93404 X0 X1
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq93404
    | exact resolve eq93404 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq93404
  have eq93488 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ (M.op X0 X0)))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq93406 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq93406
    | exact resolve eq93406 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93406
  have eq105317 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (k (τ (M.op (σ X0) (σ (M.op X0 X0)))) X0) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (k (τ (M.op (σ X0) (σ (M.op X0 X0)))) X0)) ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (k (τ (M.op (σ X0) (σ (M.op X0 X0)))) X0) (τ X1)
       have i₂ := eq93486 X0 X1
       grind)
    | exact superpose eq93486 eq14
    | (have j0 := eq14 (k (τ (M.op (σ X0) (σ (M.op X0 X0)))) X0) (τ X1)
       grind)
    | exact resolve eq14 eq93486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93486
  have eq105361 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (τ X1) = (M.op (τ X1) (k (τ (M.op (σ X0) (σ (M.op X0 X0)))) X0)) ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq105317 X0 X1
       have i₂ := eq93488 X0
       grind)
    | exact superpose eq93488 eq105317
    | (have j0 := eq105317 X0 X1
       grind)
    | exact resolve eq105317 eq93488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105317
  have eq105511 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (τ X1) = (M.op (τ X1) (k (τ (M.op (σ X0) (σ (M.op X0 X0)))) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq105361 X0 X1
       have j1 := eq12 X0 (τ X1)
       grind)
    | (have r₁ := eq105361 X0 X1
       have r₂ := eq12 X0 (τ X1)
       grind)
    | exact resolve eq105361 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105361
  have eq105643 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (τ X1) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq105511 X0 X1
       have i₂ := eq93488 X0
       grind)
    | exact superpose eq93488 eq105511
    | (have j0 := eq105511 X0 X1
       grind)
    | exact resolve eq105511 eq93488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93488 eq105511
  have eq106808 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq105643 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq105643
    | exact resolve eq105643 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105643
  have eq107636 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq106808 (σ X1) (σ X0)
       grind)
    | exact superpose eq106808 eq15
    | (have j1 := eq106808 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq106808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107661 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq106808 X1 (τ X0)
       grind)
    | exact superpose eq106808 eq17
    | (have j1 := eq106808 X1 (τ X0)
       grind)
    | exact resolve eq17 eq106808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq106808
  have eq109686 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq107661 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq107661
    | exact resolve eq107661 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107661
  have eq110113 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq109686 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq109686
    | (have j0 := eq109686 X0 X1
       grind)
    | exact resolve eq109686 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109686
  have eq121316 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq107636 x y
       grind)
    | exact superpose eq107636 eq16
    | (have j1 := eq107636 x y
       grind)
    | exact resolve eq16 eq107636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107636
  have eq122963 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq121316
       have i₂ := eq110113 x y
       grind)
    | exact superpose eq110113 eq121316
    | (have j1 := eq110113 (σ x) (σ y)
       grind)
    | (have r₁ := eq121316
       have r₂ := eq110113 x y
       grind)
    | exact resolve eq121316 eq110113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110113 eq121316
  have eq122966 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq122963
  have eq122972 : ∀ X0 : G, y = (M.op (M.op (M.op X0 y) y) y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 x
       have i₂ := eq122966
       grind)
    | exact superpose eq122966 eq9
    | exact resolve eq9 eq122966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122966
  have eq125448 : y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq122972 (M.op x y)
       have i₂ := eq122972 x
       grind)
    | exact superpose eq122972 eq122972
    | exact resolve eq122972 eq122972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122972
  have eq125530 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq125448
  have eq125557 : y = (k (τ (M.op (σ (M.op y y)) (σ y))) y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq23510 y (σ x)
       have i₂ := eq125530
       grind)
    | exact superpose eq125530 eq23510
    | (have j0 := eq23510 y x
       grind)
    | exact resolve eq23510 eq125530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23510
  have eq125586 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq19 (σ y) (σ x)
       have i₂ := eq125530
       grind)
    | exact superpose eq125530 eq19
    | exact resolve eq19 eq125530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq125530
  have eq125661 : y = (k (τ (M.op (σ (M.op y y)) (σ y))) y) ∨ y = (M.op y y) := by grind
  clear eq125557
  have eq125703 : (σ y) = (M.op (σ (M.op y y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq125586
       have i₂ := eq5635 y
       grind)
    | exact superpose eq5635 eq125586
    | exact resolve eq125586 eq5635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5635 eq125586
  have eq144903 : y = (k (τ (σ y)) y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq125661
       have i₂ := eq125703
       grind)
    | exact superpose eq125703 eq125661
    | exact resolve eq125661 eq125703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125661 eq125703
  have eq144975 : y = (k (τ (σ y)) y) ∨ y = (M.op y y) := by grind
  clear eq144903
  have eq144996 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq144975
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq144975
    | exact resolve eq144975 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144975
  have eq145014 : y = (M.op y y) := by
    first
    | (have j1 := eq228 y
       grind)
    | (have r₁ := eq144996
       have r₂ := eq228 y
       grind)
    | exact resolve eq144996 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228 eq144996
  have eq145349 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq145014
       grind)
    | exact superpose eq145014 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq145014
       grind)
    | exact resolve eq12 eq145014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145353 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq5525 y X0
       have i₂ := eq145014
       grind)
    | exact superpose eq145014 eq5525
    | (have j0 := eq5525 y X0
       grind)
    | exact resolve eq5525 eq145014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5525 eq145014
  have eq145496 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq145353 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145353
  have eq145498 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq145349 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145349
  have eq148830 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq145496 (σ X0)
       grind)
    | exact superpose eq145496 eq15
    | exact resolve eq15 eq145496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145496
  have eq149037 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq148830 X0
       have i₂ := eq145498 X0
       grind)
    | exact superpose eq145498 eq148830
    | exact resolve eq148830 eq145498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145498 eq148830
  have eq154395 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq149037 x
       grind)
    | exact superpose eq149037 eq16
    | (have r₁ := eq16
       have r₂ := eq149037 x
       grind)
    | exact resolve eq16 eq149037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149037
  have eq154673 : False := by grind
  exact eq154673

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_pyx_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
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
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22
    | exact resolve eq22 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq55 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq55
    | (have j0 := eq55 (σ X0) (σ X1)
       grind)
    | exact resolve eq55 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq94 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X4) X3) X4) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0 X4
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) X2) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (M.op X0 X1) X0 X1 (M.op (M.op X0 (M.op X0 X1)) X2)
       have i₂ := eq9 (M.op X0 X1) (M.op X0 (M.op X0 X1)) X2
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq128 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66 y x
       grind)
    | exact superpose eq66 eq16
    | (have j1 := eq66 y x
       grind)
    | exact resolve eq16 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq66 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq66 X0 X1
       grind)
    | exact resolve eq12 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq66 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq66 X0 X1
       grind)
    | exact resolve eq13 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq139 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq132 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq132 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq132 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq132 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq140 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq131 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq131 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq131 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq143 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq139 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq139
    | (have j0 := eq139 X0 X1
       grind)
    | exact resolve eq139 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq144 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq140 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq140
    | (have j0 := eq140 X0 X1
       grind)
    | exact resolve eq140 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq373 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq128
       have i₂ := eq55 y x
       grind)
    | exact superpose eq55 eq128
    | (have j1 := eq55 (σ y) (σ x)
       grind)
    | exact resolve eq128 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq128
  have eq376 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq373
  have eq378 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq376
       grind)
    | exact superpose eq376 eq9
    | exact resolve eq9 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq922 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (M.op X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq94 X0 X1 X2 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)
       have i₂ := eq9 X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3
       grind)
    | exact superpose eq9 eq94
    | exact resolve eq94 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq943 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq922 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq922
    | exact resolve eq922 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq2157 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq143 (τ X1) (τ X0)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq143
    | (have j0 := eq143 (τ X0) (τ X1)
       grind)
    | exact resolve eq143 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq143
  have eq2176 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2157 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2157
    | (have j0 := eq2157 X0 X1
       grind)
    | exact resolve eq2157 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2157
  have eq2183 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2176 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2176
    | (have j0 := eq2176 X0 X1
       grind)
    | exact resolve eq2176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2176
  have eq2188 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2183 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2183
    | (have j0 := eq2183 X0 X1
       grind)
    | exact resolve eq2183 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2183
  have eq2193 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2188 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2188
    | (have j0 := eq2188 X0 X1
       grind)
    | exact resolve eq2188 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2188
  have eq2198 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2193 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2193
    | (have j0 := eq2193 X0 X1
       grind)
    | exact resolve eq2193 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2193
  have eq2203 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2198 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2198
    | (have j0 := eq2198 X0 X1
       grind)
    | exact resolve eq2198 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2198
  have eq2323 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq378 x
       have i₂ := eq78 x
       grind)
    | exact superpose eq78 eq378
    | exact resolve eq378 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq2446 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 x x X0
       have i₂ := eq2323
       grind)
    | exact superpose eq2323 eq9
    | exact resolve eq9 eq2323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2323
  have eq3518 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq100 x X0 x
       have i₂ := eq2446 X0
       grind)
    | exact superpose eq2446 eq100
    | exact resolve eq100 eq2446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq2446
  have eq4847 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq943 (σ x) (σ y)
       have i₂ := eq3518 X0
       grind)
    | exact superpose eq3518 eq943
    | (have j1 := eq3518 X0
       grind)
    | exact resolve eq943 eq3518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3518
  have eq6213 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq12 (σ x) (σ x)
       have i₂ := eq4847 X0
       grind)
    | exact superpose eq4847 eq12
    | (have j1 := eq4847 X0
       grind)
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq4847 X0
       grind)
    | exact resolve eq12 eq4847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4847
  have eq6274 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq6213 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6213
  have eq6310 : ∀ X0 : G, (σ x) = (σ (k x x)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq6274 X0
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq6274
    | (have j0 := eq6274 X0
       grind)
    | exact resolve eq6274 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6274
  have eq6350 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq6310 X0
       grind)
    | exact superpose eq6310 eq10
    | (have j1 := eq6310 X0
       grind)
    | exact resolve eq10 eq6310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6310
  have eq6406 : ∀ X0 : G, x = (k x x) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq6350 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6350
    | (have j0 := eq6350 X0
       grind)
    | exact resolve eq6350 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6350
  have eq6428 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq2203 x x
       have i₂ := eq6406 X0
       grind)
    | exact superpose eq6406 eq2203
    | (have j0 := eq2203 x x
       have j1 := eq6406 X0
       grind)
    | (have r₁ := eq2203 x x
       have r₂ := eq6406 X0
       grind)
    | exact resolve eq2203 eq6406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6406
  have eq6429 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq6428 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6428
  have eq6430 : ∀ X0 : G, x = (M.op x x) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq6429 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6429
  have eq6449 : ∀ X0 X1 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ x = (M.op (M.op x X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x x X0
       have i₂ := eq6430 X1
       grind)
    | exact superpose eq6430 eq9
    | (have j1 := eq6430 (M.op x X0)
       grind)
    | exact resolve eq9 eq6430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6430
  have eq6547 : ∀ X0 X1 : G, x = (M.op (M.op x X0) x) ∨ x = (M.op (M.op x X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq6449 X0 X1
       have i₂ := eq943 x X0
       grind)
    | (have i₁ := eq6449 X0 X1
       have i₂ := eq943 x (M.op x X0)
       grind)
    | exact superpose eq943 eq6449
    | (have j0 := eq6449 X0 X0
       grind)
    | exact resolve eq6449 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6449
  have eq6999 : ∀ X0 : G, x ≠ x ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq6547 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6547
  have eq7000 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq6999 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6999
  have eq7030 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq378 X0
       have i₂ := eq7000 X0
       grind)
    | exact superpose eq7000 eq378
    | exact resolve eq378 eq7000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq7427 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq943 (σ x) (σ y)
       have i₂ := eq7030 X0
       grind)
    | exact superpose eq7030 eq943
    | (have j1 := eq7030 X0
       grind)
    | exact resolve eq943 eq7030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943 eq7030
  have eq7741 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 (σ x) (σ x)
       have i₂ := eq7427 X0
       grind)
    | exact superpose eq7427 eq12
    | (have j1 := eq7427 X0
       grind)
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq7427 X0
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq7427 x
       grind)
    | exact resolve eq12 eq7427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7427
  have eq7802 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7741 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7741
  have eq7838 : ∀ X0 : G, (σ x) = (σ (k x x)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7802 X0
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq7802
    | (have j0 := eq7802 X0
       grind)
    | exact resolve eq7802 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7802
  have eq8073 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq7838 X0
       grind)
    | exact superpose eq7838 eq10
    | (have j1 := eq7838 X0
       grind)
    | exact resolve eq10 eq7838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7838
  have eq8132 : ∀ X0 : G, x = (k x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8073 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8073
    | (have j0 := eq8073 X0
       grind)
    | exact resolve eq8073 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8073
  have eq8294 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2203 x x
       have i₂ := eq8132 X0
       grind)
    | exact superpose eq8132 eq2203
    | (have j0 := eq2203 x x
       have j1 := eq8132 x
       grind)
    | (have r₁ := eq2203 x x
       have r₂ := eq8132 X0
       grind)
    | exact resolve eq2203 eq8132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2203 eq8132
  have eq8295 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq8294 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8294
  have eq8296 : ∀ X0 : G, x = (M.op x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq8295 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8295
  have eq8514 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have j0 := eq8296 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8296
  have eq8515 : x = (M.op x x) := by grind
  clear eq8514
  have eq8780 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq8515
       grind)
    | exact superpose eq8515 eq9
    | exact resolve eq9 eq8515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8781 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq8515
       grind)
    | exact superpose eq8515 eq12
    | (have r₁ := eq12 x x
       have r₂ := eq8515
       grind)
    | exact resolve eq12 eq8515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8515
  have eq8843 : x = (k x x) := by grind
  clear eq8781
  have eq8895 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8780 X0
       have i₂ := eq7000 X0
       grind)
    | exact superpose eq7000 eq8780
    | exact resolve eq8780 eq7000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7000 eq8780
  have eq9106 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq144 x x
       have i₂ := eq8843
       grind)
    | exact superpose eq8843 eq144
    | exact resolve eq144 eq8843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq8843
  have eq9124 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq9106
  have eq9320 : ∀ X0 X1 : G, (M.op (M.op (M.op x X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 x X0
       have i₂ := eq8895 X0
       grind)
    | exact superpose eq8895 eq9
    | exact resolve eq9 eq8895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9496 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9320 X0 X1
       have i₂ := eq8895 X1
       grind)
    | exact superpose eq8895 eq9320
    | exact resolve eq9320 eq8895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9320
  have eq12829 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ x)
       have i₂ := eq9124
       grind)
    | exact superpose eq9124 eq9
    | exact resolve eq9 eq9124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9124
  have eq12945 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12829 X0
       have i₂ := eq9496 X0 (σ x)
       grind)
    | exact superpose eq9496 eq12829
    | exact resolve eq12829 eq9496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9496 eq12829
  have eq13022 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12945 (σ y)
       grind)
    | exact superpose eq12945 eq16
    | exact resolve eq16 eq12945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12945
  have eq13211 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq13022
       have i₂ := eq8895 y
       grind)
    | exact superpose eq8895 eq13022
    | exact resolve eq13022 eq8895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8895 eq13022
  have eq13212 : False := by grind
  exact eq13212
