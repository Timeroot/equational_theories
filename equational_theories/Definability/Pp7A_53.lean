import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_x_y_pxy_pxx_pxy_Equation3058 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
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
  clear eq23
  have eq54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq82 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq54 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq54
    | exact resolve eq54 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq89 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq83
    | (have j0 := eq83 X0
       grind)
    | exact resolve eq83 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq83
  have eq90 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq89 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq89
    | (have j0 := eq89 X0
       grind)
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq91 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq90 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq90 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq90 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq94 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq91 (σ X0)
       grind)
    | exact superpose eq91 eq15
    | exact resolve eq15 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq94 X0
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq94
    | exact resolve eq94 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq94
  have eq160 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq77 x y
       grind)
    | exact superpose eq77 eq16
    | (have j1 := eq77 x y
       grind)
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq77 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq639 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq82
    | exact resolve eq82 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq682 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq639 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq639
    | (have j0 := eq639 X0 X1
       grind)
    | exact resolve eq639 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq772 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq163 (τ X0) (τ X1)
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq163
    | (have j0 := eq163 (τ X0) (τ X1)
       grind)
    | exact resolve eq163 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq780 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq772 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq772
    | (have j0 := eq772 X0 X1
       grind)
    | exact resolve eq772 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq783 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
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
  have eq785 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq783 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq783
    | (have j0 := eq783 X0 X1
       grind)
    | exact resolve eq783 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783
  have eq786 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq785 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq785
    | (have j0 := eq785 X0 X1
       grind)
    | exact resolve eq785 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq787 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ X0 = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq786 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq786
    | (have j0 := eq786 X0 X1
       grind)
    | exact resolve eq786 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq788 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq787 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq787
    | (have j0 := eq787 X0 X1
       grind)
    | exact resolve eq787 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq1068 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq160
       have i₂ := eq682 y x
       grind)
    | exact superpose eq682 eq160
    | (have j1 := eq682 (σ x) (σ y)
       grind)
    | (have r₁ := eq160
       have r₂ := eq682 y x
       grind)
    | (have r₁ := eq160
       have r₂ := eq682 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq160
       have r₂ := eq682 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq160 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq682
  have eq1069 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1068
  have eq7575 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1069
       grind)
    | exact superpose eq1069 eq16
    | exact resolve eq16 eq1069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069
  have eq7576 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq7575
       have r₂ := eq105 x
       grind)
    | exact resolve eq7575 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7575
  have eq7640 : x ≠ x ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq7576
       grind)
    | exact superpose eq7576 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq7576
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq7576
       grind)
    | exact resolve eq12 eq7576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7576
  have eq7641 : x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7640
  have eq7645 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq163 x y
       have i₂ := eq7641
       grind)
    | exact superpose eq7641 eq163
    | (have j0 := eq163 x y
       grind)
    | exact resolve eq163 eq7641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq7641
  have eq7657 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7645
  have eq7658 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq7657
  have eq7774 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7658
       grind)
    | exact superpose eq7658 eq16
    | exact resolve eq16 eq7658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7775 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq7658
       grind)
    | exact superpose eq7658 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq7658
       grind)
    | exact resolve eq12 eq7658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7658
  have eq7776 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq7775
  have eq7778 : (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq7776
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq7776
    | exact resolve eq7776 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7776
  have eq7900 : y = (τ (σ x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq7778
       grind)
    | exact superpose eq7778 eq10
    | exact resolve eq10 eq7778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7778
  have eq7971 : x = y ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq7900
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7900
    | exact resolve eq7900 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7900
  have eq7979 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7971
       grind)
    | exact superpose eq7971 eq16
    | exact resolve eq16 eq7971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7971
  have eq7980 : (σ x) = (σ (k x y)) := by
    first
    | (have r₁ := eq7979
       have r₂ := eq105 x
       grind)
    | exact resolve eq7979 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7979
  have eq8099 : (k x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq7980
       grind)
    | exact superpose eq7980 eq10
    | exact resolve eq10 eq7980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7980
  have eq8172 : x = (k x y) := by
    first
    | (have i₁ := eq8099
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8099
    | exact resolve eq8099 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8099
  have eq8188 : x ≠ x ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq788 x y
       have i₂ := eq8172
       grind)
    | exact superpose eq8172 eq788
    | (have j0 := eq788 x y
       grind)
    | (have r₁ := eq788 x y
       have r₂ := eq8172
       grind)
    | exact resolve eq788 eq8172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788 eq8172
  have eq8193 : x = (M.op x y) ∨ x = y := by grind
  clear eq8188
  have eq8308 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq7774
       have i₂ := eq8193
       grind)
    | exact superpose eq8193 eq7774
    | exact resolve eq7774 eq8193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7774 eq8193
  have eq8311 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq8308
  have eq8312 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8311
       grind)
    | exact superpose eq8311 eq16
    | exact resolve eq16 eq8311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8311
  have eq8317 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq8312
       have r₂ := eq105 x
       grind)
    | exact resolve eq8312 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8312
  have eq8428 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8317
       grind)
    | exact superpose eq8317 eq16
    | exact resolve eq16 eq8317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8429 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq8317
       grind)
    | exact superpose eq8317 eq10
    | exact resolve eq10 eq8317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8317
  have eq8500 : x = y := by
    first
    | (have i₁ := eq8429
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8429
    | exact resolve eq8429 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8429
  have eq8501 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8428
       have i₂ := eq105 x
       grind)
    | exact superpose eq105 eq8428
    | exact resolve eq8428 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq8428
  have eq8506 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8501
       have i₂ := eq8500
       grind)
    | exact superpose eq8500 eq8501
    | exact resolve eq8501 eq8500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8500 eq8501
  have eq8507 : False := by grind
  exact eq8507

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyx_pyx_pxx_pyx_Equation3058 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
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
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
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
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq44 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq44 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq45 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq45 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq46 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq46 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       have j1 := eq49 X1 X0
       grind)
    | (have r₁ := eq52 X0 X1
       have r₂ := eq49 X0 X1
       grind)
    | (have r₁ := eq52 X1 X0
       have r₂ := eq49 X0 X1
       grind)
    | exact resolve eq52 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq52
  have eq64 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1
       have i₂ := eq19 X1
       grind)
    | exact superpose eq19 eq54
    | (have j0 := eq54 X0 X1
       grind)
    | exact resolve eq54 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq54
  have eq120 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq124 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq120 X0 X1
       have j1 := eq64 X1 X0
       grind)
    | (have r₁ := eq120 X1 X0
       have r₂ := eq64 X0 X1
       grind)
    | (have r₁ := eq120 X1 X1
       have r₂ := eq64 X1 X1
       grind)
    | exact resolve eq120 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq120
  have eq306 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq124 (σ X1) (σ X0)
       grind)
    | exact superpose eq124 eq15
    | exact resolve eq15 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq313 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq306 X0 X1
       have i₂ := eq124 X1 X0
       grind)
    | exact superpose eq124 eq306
    | exact resolve eq306 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq306
  have eq316 : False := by grind
  exact eq316

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyx_y_pyx_Equation3058 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq61 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq61 (σ X0)
       grind)
    | exact superpose eq61 eq15
    | exact resolve eq15 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq61 X0
       grind)
    | exact superpose eq61 eq64
    | exact resolve eq64 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq64
  have eq89 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq480 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq463 X0 X1
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq463
    | (have j0 := eq463 X0 X1
       grind)
    | exact resolve eq463 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq639 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq480 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq480
    | exact resolve eq480 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq665 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq639 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq639
    | (have j0 := eq639 X0 X1
       grind)
    | exact resolve eq639 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq671 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq665 X0 X1
       have j1 := eq89 X1 X0
       grind)
    | (have r₁ := eq665 X1 X0
       have r₂ := eq89 X0 X1
       grind)
    | exact resolve eq665 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq674 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq671 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq671
    | exact resolve eq671 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq686 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X1 X0
       have i₂ := eq671 X0 X1
       grind)
    | exact superpose eq671 eq89
    | (have j0 := eq89 X0 X1
       have j1 := eq671 X1 X0
       grind)
    | exact resolve eq89 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq697 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq671 X0 X1
       grind)
    | exact superpose eq671 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq671 (σ X0) X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq671 X0 X1
       grind)
    | exact resolve eq13 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq699 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq697 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq701 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (k X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq699 X0 X1
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq699
    | (have j0 := eq699 X0 X1
       grind)
    | exact resolve eq699 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq699
  have eq707 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq701 X0 X1
       have j1 := eq686 X0 X1
       grind)
    | (have r₁ := eq701 X0 X1
       have r₂ := eq686 X0 X1
       grind)
    | exact resolve eq701 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686 eq701
  have eq738 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq707 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq707
    | exact resolve eq707 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq805 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq738 X0 (τ X1)
       grind)
    | exact superpose eq738 eq17
    | (have j1 := eq738 X0 (τ X1)
       grind)
    | exact resolve eq17 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq811 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq738 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq1204 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq805 (τ X0) X1
       grind)
    | exact superpose eq805 eq18
    | (have j1 := eq805 (τ X0) X1
       grind)
    | exact resolve eq18 eq805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq805
  have eq1213 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1204 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1204
    | (have j0 := eq1204 X0 X1
       grind)
    | exact resolve eq1204 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204
  have eq1225 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1213 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1213
    | (have j0 := eq1213 X0 X1
       grind)
    | exact resolve eq1213 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213
  have eq1227 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1225 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1225
    | (have j0 := eq1225 X0 X1
       grind)
    | exact resolve eq1225 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1291 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1227 X0 X1
       have i₂ := eq674 X0 X1
       grind)
    | exact superpose eq674 eq1227
    | (have j1 := eq674 X0 X1
       grind)
    | exact resolve eq1227 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227
  have eq1332 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1291 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1291
  have eq1476 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq811 X1 X0
       have i₂ := eq1332 X0 X1
       grind)
    | exact superpose eq1332 eq811
    | (have j0 := eq811 X1 X0
       have j1 := eq1332 X0 X1
       grind)
    | (have r₁ := eq811 X1 X0
       have r₂ := eq1332 X0 X1
       grind)
    | exact resolve eq811 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq1495 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op (τ (σ x)) (τ (σ y)))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1332 (σ x) (σ y)
       grind)
    | exact superpose eq1332 eq16
    | (have j1 := eq1332 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332
  have eq1512 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1476 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1476
  have eq1523 : (M.op (σ x) (σ y)) = (σ (M.op (τ (σ x)) y)) ∨ (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq1495
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1495
    | exact resolve eq1495 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1495
  have eq1555 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq1523
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1523
    | exact resolve eq1523 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1523
  have eq1567 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have r₁ := eq1555
       have r₂ := eq16
       grind)
    | exact resolve eq1555 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1555
  have eq1742 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq1512 (σ X0) X1
       grind)
    | exact superpose eq1512 eq22
    | (have j1 := eq1512 (σ X0) X1
       grind)
    | exact resolve eq22 eq1512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1512
  have eq1783 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1742 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1742
    | (have j0 := eq1742 X0 X1
       grind)
    | exact resolve eq1742 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1742
  have eq1801 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1783 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1783
    | (have j0 := eq1783 X0 X1
       grind)
    | exact resolve eq1783 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1783
  have eq2954 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1801 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1801
    | exact resolve eq1801 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1801
  have eq3062 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2954 y x
       grind)
    | exact superpose eq2954 eq16
    | (have j1 := eq2954 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq2954 y x
       grind)
    | exact resolve eq16 eq2954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2954
  have eq3090 : x = (k y x) := by grind
  clear eq3062
  have eq3140 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq674 x y
       have i₂ := eq3090
       grind)
    | exact superpose eq3090 eq674
    | (have j0 := eq674 x y
       grind)
    | exact resolve eq674 eq3090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674 eq3090
  have eq3143 : x = (M.op x y) := by grind
  clear eq3140
  have eq3149 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1567
       have i₂ := eq3143
       grind)
    | exact superpose eq3143 eq1567
    | exact resolve eq1567 eq3143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1567 eq3143
  have eq3157 : False := by grind
  exact eq3157

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_pxx_pyx_Equation3058 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  clear eq62 eq65
  have eq90 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
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
  have eq395 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq412 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq395 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq395
    | (have j0 := eq395 X0 X1
       grind)
    | exact resolve eq395 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq698 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq412 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq412
    | exact resolve eq412 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq712 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq698 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq698
    | (have j0 := eq698 X0 X1
       grind)
    | exact resolve eq698 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq698
  have eq719 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq712 X0 X1
       have j1 := eq90 X1 X0
       grind)
    | (have r₁ := eq712 X1 X0
       have r₂ := eq90 X0 X1
       grind)
    | (have r₁ := eq712 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq712 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq712
  have eq722 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq719 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq719
    | exact resolve eq719 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq736 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq719 (σ X1) X0
       grind)
    | exact superpose eq719 eq15
    | (have j1 := eq719 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq769 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq722 (τ X0) X1
       grind)
    | exact superpose eq722 eq19
    | (have j1 := eq722 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq722
  have eq862 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq769 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq769
    | exact resolve eq769 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq904 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq862 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq862
    | (have j0 := eq862 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq862 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq1085 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq736 x y
       grind)
    | exact superpose eq736 eq16
    | (have j1 := eq736 x y
       grind)
    | exact resolve eq16 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq1101 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1085
       have i₂ := eq904 x y
       grind)
    | exact superpose eq904 eq1085
    | (have j1 := eq904 (σ x) (σ y)
       grind)
    | (have r₁ := eq1085
       have r₂ := eq904 x y
       grind)
    | (have r₁ := eq1085
       have r₂ := eq904 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1085
       have r₂ := eq904 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1085 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904 eq1085
  have eq1102 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1101
  have eq1105 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1102
       grind)
    | exact superpose eq1102 eq16
    | exact resolve eq16 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq1106 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1105
       have r₂ := eq76 x
       grind)
    | exact resolve eq1105 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105
  have eq1107 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1106
       grind)
    | exact superpose eq1106 eq16
    | exact resolve eq16 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1108 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1106
       grind)
    | exact superpose eq1106 eq10
    | exact resolve eq10 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106
  have eq1154 : x = y := by
    first
    | (have i₁ := eq1108
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1108
    | exact resolve eq1108 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108
  have eq1155 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1107
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq1107
    | exact resolve eq1107 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq1107
  have eq1156 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1155
       have i₂ := eq1154
       grind)
    | exact superpose eq1154 eq1155
    | exact resolve eq1155 eq1154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154 eq1155
  have eq1157 : False := by grind
  exact eq1157

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_y_pxy_Equation3058 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq37 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq86 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq29
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq217 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq85 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq654 : ∀ X0 X1 : G, (σ (σ (k X0 X1))) ≠ (σ (σ X1)) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq217 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq217
    | (have j0 := eq217 (σ X0) (σ X1)
       grind)
    | exact resolve eq217 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq2651 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq86 X1 X0
       grind)
    | exact superpose eq86 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq86 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq86 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq86 X0 (σ X0)
       grind)
    | exact resolve eq13 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2652 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq86 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq2653 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2652 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2652
  have eq2654 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2651 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2651
  have eq2655 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2654 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2654
  have eq2658 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2653 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2653
    | (have j0 := eq2653 X0
       grind)
    | exact resolve eq2653 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2653
  have eq2690 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq2658 X0
       grind)
    | exact superpose eq2658 eq37
    | (have j1 := eq2658 X0
       grind)
    | exact resolve eq37 eq2658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2658
  have eq2698 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2690 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2690
    | (have j0 := eq2690 X0
       grind)
    | exact resolve eq2690 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2690
  have eq2699 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2698 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2698
  have eq2701 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2699 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2699
    | exact resolve eq2699 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2723 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq2699 X0
       grind)
    | exact superpose eq2699 eq11
    | exact resolve eq11 eq2699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2699
  have eq2765 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2701 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq2701
    | exact resolve eq2701 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2701
  have eq2960 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq2765 X0
       grind)
    | exact superpose eq2765 eq11
    | exact resolve eq11 eq2765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3034 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2960 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq2960
    | exact resolve eq2960 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2960
  have eq3091 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq3034 (τ X0)
       grind)
    | exact superpose eq3034 eq33
    | exact resolve eq33 eq3034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3136 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3091 X0
       have i₂ := eq2765 X0
       grind)
    | exact superpose eq2765 eq3091
    | exact resolve eq3091 eq2765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2765 eq3091
  have eq3616 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq3621 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq3616 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq3616
    | exact resolve eq3616 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3616
  have eq3649 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3621 X0
       have i₂ := eq3034 X0
       grind)
    | exact superpose eq3034 eq3621
    | exact resolve eq3621 eq3034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3621
  have eq3662 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq3649
  have eq25041 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X1) X0
       have i₂ := eq2655 (σ X0) X1
       grind)
    | exact superpose eq2655 eq23
    | (have j1 := eq2655 (σ X0) X1
       grind)
    | exact resolve eq23 eq2655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2655
  have eq25124 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq25041 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq25041
    | (have j0 := eq25041 X0 X1
       grind)
    | exact resolve eq25041 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25041
  have eq25204 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq25124 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25124
    | (have j0 := eq25124 X0 X1
       grind)
    | exact resolve eq25124 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25124
  have eq25275 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq25204 X0 X1
       have i₂ := eq2723 X0
       grind)
    | exact superpose eq2723 eq25204
    | (have j0 := eq25204 X0 X1
       grind)
    | exact resolve eq25204 eq2723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25204
  have eq25324 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq25275 X0 X1
       have i₂ := eq3034 X0
       grind)
    | exact superpose eq3034 eq25275
    | (have j0 := eq25275 X0 X1
       grind)
    | exact resolve eq25275 eq3034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25275
  have eq25363 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25324 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25324
    | (have j0 := eq25324 X0 X1
       grind)
    | exact resolve eq25324 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25324
  have eq27001 : ∀ X0 X1 : G, (σ (σ (τ X1))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq654 (τ X0) (τ X1)
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq654
    | (have j0 := eq654 (τ X0) (τ X1)
       grind)
    | exact resolve eq654 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq27076 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X1))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq27001 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq27001
    | (have j0 := eq27001 X0 X1
       grind)
    | exact resolve eq27001 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27001
  have eq27130 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq27076 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq27076
    | (have j0 := eq27076 X0 X1
       grind)
    | exact resolve eq27076 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27076
  have eq27182 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (σ (τ X0))) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq27130 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27130
    | (have j0 := eq27130 X0 X1
       grind)
    | exact resolve eq27130 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27130
  have eq27231 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq27182 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27182
    | (have j0 := eq27182 X0 X1
       grind)
    | exact resolve eq27182 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27182
  have eq27271 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) (σ (τ X1)))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq27231 X0 X1
       have i₂ := eq2723 (σ (τ X1))
       grind)
    | exact superpose eq2723 eq27231
    | (have j0 := eq27231 X0 X1
       grind)
    | exact resolve eq27231 eq2723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2723 eq27231
  have eq27310 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (σ (k (τ X1) (τ X1)))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq27271 X0 X1
       have i₂ := eq15 (τ X1) (τ X1)
       grind)
    | exact superpose eq15 eq27271
    | (have j0 := eq27271 X0 X1
       grind)
    | exact resolve eq27271 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27271
  have eq27347 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq27310 X0 X1
       have i₂ := eq19 X1 (τ X1)
       grind)
    | exact superpose eq19 eq27310
    | (have j0 := eq27310 X0 X1
       grind)
    | exact resolve eq27310 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq27310
  have eq27377 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq27347 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq27347
    | (have j0 := eq27347 X0 X1
       grind)
    | exact resolve eq27347 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27347
  have eq27403 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq27377 X0 X1
       have i₂ := eq3034 X1
       grind)
    | exact superpose eq3034 eq27377
    | (have j0 := eq27377 X0 X1
       grind)
    | exact resolve eq27377 eq3034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3034 eq27377
  have eq27429 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27403 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27403
    | (have j0 := eq27403 X0 X1
       grind)
    | exact resolve eq27403 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27403
  have eq30907 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (σ (M.op X1 X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq25363 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25363
    | (have j0 := eq25363 X1 (τ X0)
       grind)
    | exact resolve eq25363 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30991 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq25363 X1 X0
       grind)
    | exact superpose eq25363 eq11
    | (have j1 := eq25363 X1 X0
       grind)
    | exact resolve eq11 eq25363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25363
  have eq31851 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (σ (M.op (τ X1) (τ X1))) = X0 ∨ (τ (k X0 X1)) = (τ (M.op X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq30907 X1 (τ X0)
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq30907
    | (have j0 := eq30907 X0 (τ X1)
       grind)
    | exact resolve eq30907 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq30907
  have eq32050 : ∀ X0 X1 : G, (σ (τ (M.op X1 X1))) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq31851 X0 X1
       have i₂ := eq3136 X1
       grind)
    | exact superpose eq3136 eq31851
    | (have j0 := eq31851 X0 X1
       grind)
    | exact resolve eq31851 eq3136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3136 eq31851
  have eq32138 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq32050 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq32050
    | (have j0 := eq32050 X0 X1
       grind)
    | exact resolve eq32050 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32050
  have eq32214 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32138 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq32138
    | (have j0 := eq32138 X0 X1
       grind)
    | exact resolve eq32138 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32138
  have eq32629 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq32214 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32214
  have eq35232 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30991 x y
       grind)
    | exact superpose eq30991 eq16
    | (have j1 := eq30991 x y
       grind)
    | exact resolve eq16 eq30991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30991
  have eq36143 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq35232
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq35232
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq35232 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35232
  have eq36146 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq36143
  have eq36147 : y = (M.op x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq36146
  have eq36150 : (τ y) ≠ (τ y) ∨ x = (M.op y y) ∨ (τ y) = (τ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq32629 x y
       have i₂ := eq36147
       grind)
    | exact superpose eq36147 eq32629
    | (have j0 := eq32629 x y
       grind)
    | exact resolve eq32629 eq36147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32629
  have eq36154 : (τ y) ≠ (τ y) ∨ x = (M.op y y) ∨ (τ y) = (τ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq36150
  have eq36155 : x = (M.op y y) ∨ (τ y) = (τ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq36154
  have eq36627 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ y) = (τ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3662 y
       have i₂ := eq36155
       grind)
    | exact superpose eq36155 eq3662
    | exact resolve eq3662 eq36155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36155
  have eq36654 : (σ x) = (σ (M.op y y)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have r₁ := eq36627
       have r₂ := eq16
       grind)
    | exact resolve eq36627 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36627
  have eq37306 : (M.op y y) = (τ (σ x)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq36654
       grind)
    | exact superpose eq36654 eq10
    | exact resolve eq10 eq36654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36654
  have eq37437 : x = (M.op y y) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq37306
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq37306
    | exact resolve eq37306 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37306
  have eq37514 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq3662 y
       have i₂ := eq37437
       grind)
    | exact superpose eq37437 eq3662
    | exact resolve eq3662 eq37437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37437
  have eq37541 : (τ y) = (τ (k x y)) := by
    first
    | (have r₁ := eq37514
       have r₂ := eq16
       grind)
    | exact resolve eq37514 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37514
  have eq38102 : (k x y) = (σ (τ y)) := by
    first
    | (have i₁ := eq11 (k x y)
       have i₂ := eq37541
       grind)
    | exact superpose eq37541 eq11
    | exact resolve eq11 eq37541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37541
  have eq38294 : y = (k x y) := by
    first
    | (have i₁ := eq38102
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq38102
    | exact resolve eq38102 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38102
  have eq38372 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq27429 x y
       have i₂ := eq38294
       grind)
    | exact superpose eq38294 eq27429
    | (have j0 := eq27429 x y
       grind)
    | exact resolve eq27429 eq38294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27429 eq38294
  have eq38373 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq38372
  have eq42239 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38373
       grind)
    | exact superpose eq38373 eq16
    | exact resolve eq16 eq38373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38373
  have eq42957 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq42239
       have i₂ := eq36147
       grind)
    | exact superpose eq36147 eq42239
    | exact resolve eq42239 eq36147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36147 eq42239
  have eq42958 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq42957
  have eq42959 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq42958
  have eq42977 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3662 y
       have i₂ := eq42959
       grind)
    | exact superpose eq42959 eq3662
    | exact resolve eq3662 eq42959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42959
  have eq43005 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq42977
       have r₂ := eq16
       grind)
    | exact resolve eq42977 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42977
  have eq43635 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq43005
       grind)
    | exact superpose eq43005 eq10
    | exact resolve eq10 eq43005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43005
  have eq43768 : x = (M.op y y) := by
    first
    | (have i₁ := eq43635
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq43635
    | exact resolve eq43635 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43635
  have eq43863 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3662 y
       have i₂ := eq43768
       grind)
    | exact superpose eq43768 eq3662
    | exact resolve eq3662 eq43768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3662 eq43768
  have eq43890 : False := by grind
  exact eq43890

/-- `Equation3071`: `x = (((x ◇ y) ◇ x) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_pxy_pxy_pxx_pxy_Equation3071 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3071 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3071.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq20 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X1)
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq12
    | (have r₁ := eq12 X0 (M.op X0 X1)
       have r₂ := eq20 X0 X1
       grind)
    | exact resolve eq12 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq41 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq44 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq44 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq44 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq47 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq45 (σ X0)
       grind)
    | exact superpose eq45 eq15
    | exact resolve eq15 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq45 (τ X0)
       grind)
    | exact superpose eq45 eq18
    | exact resolve eq18 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq49 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq49
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq52 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq47
    | exact resolve eq47 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq50 X0
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq50
    | exact resolve eq50 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq50
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0 X1
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq70
    | (have j0 := eq70 X0 X1
       grind)
    | exact resolve eq70 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq83 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (k X0 (τ (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 (M.op (σ X0) X1)
       have i₂ := eq31 (σ X0) X1
       grind)
    | exact superpose eq31 eq41
    | exact resolve eq41 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq41
  have eq215 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq77
    | exact resolve eq77 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq77 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq245 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq215 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq215
    | (have j0 := eq215 X0 X1
       grind)
    | exact resolve eq215 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq215
  have eq250 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq245 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq245 X0 (M.op (τ X0) (τ X0))
       have r₂ := eq12 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | (have r₁ := eq245 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq245 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq253 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq250 X0 X1
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq250
    | (have j0 := eq250 X0 X1
       grind)
    | exact resolve eq250 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq250
  have eq701 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq253 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq253
    | exact resolve eq253 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq719 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq253 (σ X0) X1
       grind)
    | exact superpose eq253 eq15
    | (have j1 := eq253 (σ X0) X1
       grind)
    | exact resolve eq15 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq738 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq719 X0 X1
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq719
    | (have j0 := eq719 X0 X1
       grind)
    | exact resolve eq719 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq786 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq701 (τ X1) X0
       grind)
    | exact superpose eq701 eq18
    | (have j1 := eq701 (τ X1) X0
       grind)
    | exact resolve eq18 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq701
  have eq2714 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq786 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq786
    | exact resolve eq786 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq2786 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2714 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2714
    | (have j0 := eq2714 X0 X1
       grind)
    | exact resolve eq2714 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2714
  have eq9799 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq738 x y
       grind)
    | exact superpose eq738 eq16
    | (have j1 := eq738 x y
       grind)
    | exact resolve eq16 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9843 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq738 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq9897 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq9799
       have i₂ := eq2786 y x
       grind)
    | exact superpose eq2786 eq9799
    | (have j1 := eq2786 y x
       grind)
    | (have r₁ := eq9799
       have r₂ := eq2786 y x
       grind)
    | exact resolve eq9799 eq2786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9799
  have eq9898 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq9897
  have eq10057 : y ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq9898
       grind)
    | exact superpose eq9898 eq12
    | exact resolve eq12 eq9898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10058 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq9898
       grind)
    | exact superpose eq9898 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq9898
       grind)
    | exact resolve eq13 eq9898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9898
  have eq10069 : (k x y) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq10058
  have eq10070 : (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq10057
       have r₂ := eq10069
       grind)
    | exact resolve eq10057 eq10069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10057 eq10069
  have eq10080 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq235 x y
       have i₂ := eq10070
       grind)
    | exact superpose eq10070 eq235
    | (have j0 := eq235 x y
       grind)
    | exact resolve eq235 eq10070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq10096 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10080
  have eq10097 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq10096
  have eq10284 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10097
       grind)
    | exact superpose eq10097 eq16
    | exact resolve eq16 eq10097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10289 : (τ (σ y)) = (k x (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq83 x (σ y)
       have i₂ := eq10097
       grind)
    | exact superpose eq10097 eq83
    | exact resolve eq83 eq10097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq10097
  have eq10308 : y = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10289
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq10289
    | exact resolve eq10289 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10289
  have eq10319 : y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10070
       have i₂ := eq10308
       grind)
    | exact superpose eq10308 eq10070
    | exact resolve eq10070 eq10308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10070 eq10308
  have eq10352 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq10319
  have eq10461 : (σ y) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq10352
       grind)
    | exact superpose eq10352 eq12
    | exact resolve eq12 eq10352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10462 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq10352
       grind)
    | exact superpose eq10352 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq10352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10352
  have eq10474 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq10462
       have r₂ := eq52 x
       grind)
    | exact resolve eq10462 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10462
  have eq10475 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) ≠ (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10461
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq10461
    | exact resolve eq10461 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10461
  have eq10477 : (σ (k x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10474
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq10474
    | exact resolve eq10474 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10474
  have eq10478 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10477
       have i₂ := eq52 x
       grind)
    | exact superpose eq52 eq10477
    | exact resolve eq10477 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10477
  have eq10479 : y = (M.op x x) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq10478
       have r₂ := eq10475
       grind)
    | exact resolve eq10478 eq10475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10475 eq10478
  have eq10618 : y = (M.op x y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq20 x x
       have i₂ := eq10479
       grind)
    | exact superpose eq10479 eq20
    | exact resolve eq20 eq10479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq10479
  have eq10798 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10284
       have i₂ := eq10618
       grind)
    | exact superpose eq10618 eq10284
    | exact resolve eq10284 eq10618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10284 eq10618
  have eq10801 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq10798
  have eq10802 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have j1 := eq9843 x y
       grind)
    | (have r₁ := eq10801
       have r₂ := eq9843 x y
       grind)
    | exact resolve eq10801 eq9843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9843 eq10801
  have eq10888 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10802
       grind)
    | exact superpose eq10802 eq16
    | exact resolve eq16 eq10802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10893 : (σ y) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq10802
       grind)
    | exact superpose eq10802 eq12
    | exact resolve eq12 eq10802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10894 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq10802
       grind)
    | exact superpose eq10802 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq10802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10802
  have eq10906 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq10894
       have r₂ := eq52 x
       grind)
    | exact resolve eq10894 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10894
  have eq10907 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq10893
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq10893
    | exact resolve eq10893 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10893
  have eq10909 : (σ (k x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10906
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq10906
    | exact resolve eq10906 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10906
  have eq10910 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10909
       have i₂ := eq52 x
       grind)
    | exact superpose eq52 eq10909
    | exact resolve eq10909 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq10909
  have eq10911 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq10910
       have r₂ := eq10907
       grind)
    | exact resolve eq10910 eq10907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10907 eq10910
  have eq11149 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2786 y x
       have i₂ := eq10911
       grind)
    | exact superpose eq10911 eq2786
    | (have j0 := eq2786 y x
       grind)
    | exact resolve eq2786 eq10911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2786 eq10911
  have eq11229 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq11149
       have r₂ := eq10888
       grind)
    | exact resolve eq11149 eq10888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11149
  have eq11485 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq10888
       have i₂ := eq11229
       grind)
    | exact superpose eq11229 eq10888
    | exact resolve eq10888 eq11229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10888 eq11229
  have eq11504 : False := by grind
  exact eq11504

/-- `Equation3071`: `x = (((x ◇ y) ◇ x) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_pyy_pxy_pyy_pxy_Equation3071 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3071 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3071.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq23 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq23 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq23 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq23 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
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
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq37 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq41 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X1 X1
       grind)
    | (have r₁ := eq37 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq39 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq40 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq40 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq45
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       have j1 := eq41 X1 X0
       grind)
    | (have r₁ := eq49 X1 X1
       have r₂ := eq41 X0 X1
       grind)
    | exact resolve eq49 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq49
  have eq165 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq170 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq165 X0 X1
       have j1 := eq51 X0 X1
       grind)
    | (have r₁ := eq165 X0 X1
       have r₂ := eq51 X0 X1
       grind)
    | (have r₁ := eq165 X0 X0
       have r₂ := eq51 X0 X0
       grind)
    | exact resolve eq165 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq165
  have eq312 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq170 (σ X0) (σ X1)
       grind)
    | exact superpose eq170 eq15
    | exact resolve eq15 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq315 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq312 X0 X1
       have i₂ := eq170 X0 X1
       grind)
    | exact superpose eq170 eq312
    | exact resolve eq312 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170 eq312
  have eq319 : False := by grind
  exact eq319

/-- `Equation3071`: `x = (((x ◇ y) ◇ x) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation3071 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3071 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3071.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq63
  have eq73 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq68 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq68 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq68 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq76 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq73 (σ X0)
       grind)
    | exact superpose eq73 eq15
    | exact resolve eq15 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq76 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq76
    | exact resolve eq76 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq76
  have eq105 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq87 X0
       grind)
    | exact superpose eq87 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq183 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq174 X0 X1
       have i₂ := eq87 X1
       grind)
    | exact superpose eq87 eq174
    | (have j0 := eq174 X0 X1
       grind)
    | exact resolve eq174 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq602 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq183 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq183
    | (have j0 := eq183 (M.op X1 X1) X1
       grind)
    | exact resolve eq183 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq622 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq602 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq602
    | (have j0 := eq602 (σ (M.op X1 X1)) X1
       grind)
    | exact resolve eq602 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq602
  have eq626 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq622 X0 X1
       have j1 := eq105 X1 X0
       grind)
    | (have r₁ := eq622 X0 X0
       have r₂ := eq105 X0 X1
       grind)
    | (have r₁ := eq622 (σ (M.op X0 X0)) X0
       have r₂ := eq105 X0 X1
       grind)
    | (have r₁ := eq622 (σ X0) (M.op X0 X0)
       have r₂ := eq105 X0 X1
       grind)
    | exact resolve eq622 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq622
  have eq628 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq626 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq626
    | exact resolve eq626 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq639 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq626 (σ X0) X1
       grind)
    | exact superpose eq626 eq15
    | (have j1 := eq626 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq668 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq628 (τ X1) X0
       grind)
    | exact superpose eq628 eq19
    | (have j1 := eq628 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq628
  have eq752 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq668 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq668
    | exact resolve eq668 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq802 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq752 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq752
    | (have j0 := eq752 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq752 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq965 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq639 x y
       grind)
    | exact superpose eq639 eq16
    | (have j1 := eq639 x y
       grind)
    | exact resolve eq16 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq980 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq965
       have i₂ := eq802 y x
       grind)
    | exact superpose eq802 eq965
    | (have j1 := eq802 (σ x) (σ y)
       grind)
    | (have r₁ := eq965
       have r₂ := eq802 y x
       grind)
    | (have r₁ := eq965
       have r₂ := eq802 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq965
       have r₂ := eq802 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq965 eq802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802 eq965
  have eq981 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq980
  have eq984 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq981
       grind)
    | exact superpose eq981 eq16
    | exact resolve eq16 eq981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981
  have eq985 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq984
       have r₂ := eq87 x
       grind)
    | exact resolve eq984 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984
  have eq986 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq985
       grind)
    | exact superpose eq985 eq16
    | exact resolve eq16 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq987 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq985
       grind)
    | exact superpose eq985 eq10
    | exact resolve eq10 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq1032 : x = y := by
    first
    | (have i₁ := eq987
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq987
    | exact resolve eq987 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq1033 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq986
       have i₂ := eq87 x
       grind)
    | exact superpose eq87 eq986
    | exact resolve eq986 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq986
  have eq1034 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1033
       have i₂ := eq1032
       grind)
    | exact superpose eq1032 eq1033
    | exact resolve eq1033 eq1032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032 eq1033
  have eq1035 : False := by grind
  exact eq1035
