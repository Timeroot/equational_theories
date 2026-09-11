import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyx_pxx_pyx_Equation3058 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq79 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
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
    | (have r₁ := eq90 X0
       have r₂ := eq12 X0 X0
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
  have eq160 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
  have eq163 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq77 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq639 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq79
    | exact resolve eq79 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq682 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq639 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq639
    | (have j0 := eq639 X0 X1
       grind)
    | exact resolve eq639 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq772 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq163 (τ X1) (τ X0)
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
  have eq780 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
  have eq783 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq780 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq780
    | (have j0 := eq780 X0 X1
       grind)
    | exact resolve eq780 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq785 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
  have eq786 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
  have eq787 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ X0 = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq786 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq786
    | (have j0 := eq786 X0 X1
       grind)
    | exact resolve eq786 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq788 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq787 X0 X0
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
       have r₂ := eq682 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq160
       have r₂ := eq682 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq160 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq682
  have eq1069 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1068
  have eq7582 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
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
  have eq7583 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq7582
       have r₂ := eq105 x
       grind)
    | exact resolve eq7582 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7582
  have eq7647 : x ≠ x ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq7583
       grind)
    | exact superpose eq7583 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq7583
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq7583
       grind)
    | exact resolve eq12 eq7583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7583
  have eq7648 : x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7647
  have eq7652 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq163 x y
       have i₂ := eq7648
       grind)
    | exact superpose eq7648 eq163
    | (have j0 := eq163 x y
       grind)
    | exact resolve eq163 eq7648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq7648
  have eq7664 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7652
  have eq7665 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq7664
  have eq7781 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7665
       grind)
    | exact superpose eq7665 eq16
    | exact resolve eq16 eq7665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7782 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq7665
       grind)
    | exact superpose eq7665 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq7665
       grind)
    | exact resolve eq12 eq7665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7665
  have eq7783 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq7782
  have eq7785 : (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq7783
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq7783
    | exact resolve eq7783 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7783
  have eq7907 : y = (τ (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq7785
       grind)
    | exact superpose eq7785 eq10
    | exact resolve eq10 eq7785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7785
  have eq7978 : x = y ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq7907
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7907
    | exact resolve eq7907 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7907
  have eq7986 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7978
       grind)
    | exact superpose eq7978 eq16
    | exact resolve eq16 eq7978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7978
  have eq7987 : (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq7986
       have r₂ := eq105 x
       grind)
    | exact resolve eq7986 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7986
  have eq8106 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq7987
       grind)
    | exact superpose eq7987 eq10
    | exact resolve eq10 eq7987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7987
  have eq8179 : x = (k y x) := by
    first
    | (have i₁ := eq8106
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8106
    | exact resolve eq8106 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8106
  have eq8195 : x ≠ x ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq788 y x
       have i₂ := eq8179
       grind)
    | exact superpose eq8179 eq788
    | (have j0 := eq788 x y
       grind)
    | (have r₁ := eq788 y x
       have r₂ := eq8179
       grind)
    | exact resolve eq788 eq8179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788 eq8179
  have eq8200 : x = (M.op x y) ∨ x = y := by grind
  clear eq8195
  have eq8315 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq7781
       have i₂ := eq8200
       grind)
    | exact superpose eq8200 eq7781
    | exact resolve eq7781 eq8200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7781 eq8200
  have eq8318 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq8315
  have eq8319 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8318
       grind)
    | exact superpose eq8318 eq16
    | exact resolve eq16 eq8318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8318
  have eq8324 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq8319
       have r₂ := eq105 x
       grind)
    | exact resolve eq8319 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8319
  have eq8435 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8324
       grind)
    | exact superpose eq8324 eq16
    | exact resolve eq16 eq8324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8436 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq8324
       grind)
    | exact superpose eq8324 eq10
    | exact resolve eq10 eq8324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8324
  have eq8507 : x = y := by
    first
    | (have i₁ := eq8436
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8436
    | exact resolve eq8436 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8436
  have eq8508 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8435
       have i₂ := eq105 x
       grind)
    | exact superpose eq105 eq8435
    | exact resolve eq8435 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq8435
  have eq8513 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8508
       have i₂ := eq8507
       grind)
    | exact superpose eq8507 eq8508
    | exact resolve eq8508 eq8507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8507 eq8508
  have eq8514 : False := by grind
  exact eq8514

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxy_pyx_Equation3058 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq83 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq133 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq83 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq83 X0 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq142 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq133 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq143 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq142 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq147 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq143 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq143
    | (have j0 := eq143 X0 X1
       grind)
    | exact resolve eq143 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq148 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq147 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq507 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq148 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq148
    | exact resolve eq148 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq521 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq148 x y
       grind)
    | exact superpose eq148 eq16
    | (have j1 := eq148 x y
       grind)
    | exact resolve eq16 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq536 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq507 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq507
    | (have j0 := eq507 X0 X1
       grind)
    | exact resolve eq507 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq507
  have eq537 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq536 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq536
    | exact resolve eq536 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq596 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq537 (τ X1) X0
       grind)
    | exact superpose eq537 eq18
    | (have j1 := eq537 (τ X1) X0
       grind)
    | exact resolve eq18 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq537
  have eq839 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq596 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq596
    | exact resolve eq596 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq894 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq839 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq839
    | (have j0 := eq839 X0 X1
       grind)
    | exact resolve eq839 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq1005 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq521
       have i₂ := eq894 y x
       grind)
    | exact superpose eq894 eq521
    | (have j1 := eq894 (σ y) (σ x)
       grind)
    | (have r₁ := eq521
       have r₂ := eq894 y x
       grind)
    | exact resolve eq521 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1006 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1005
  have eq1011 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1006
  have eq1070 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq521
       have i₂ := eq1011
       grind)
    | exact superpose eq1011 eq521
    | exact resolve eq521 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521 eq1011
  have eq1071 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1070
  have eq1072 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1071
  have eq1085 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1072
  have eq1097 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1085
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1085
    | exact resolve eq1085 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085
  have eq1155 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1097
       grind)
    | exact superpose eq1097 eq16
    | exact resolve eq16 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097
  have eq1161 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1155
       have i₂ := eq894 y x
       grind)
    | exact superpose eq894 eq1155
    | (have j1 := eq894 y x
       grind)
    | (have r₁ := eq1155
       have r₂ := eq894 y x
       grind)
    | exact resolve eq1155 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq1162 : y = (M.op x x) := by grind
  clear eq1161
  have eq1222 : (M.op x y) = (k y x) := by grind
  clear eq1162
  have eq1228 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1155
       have i₂ := eq1222
       grind)
    | exact superpose eq1222 eq1155
    | exact resolve eq1155 eq1222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155 eq1222
  have eq1231 : False := by grind
  exact eq1231

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyx_pxy_Equation3058 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq53 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq53 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq53 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq54 (σ X0)
       grind)
    | exact superpose eq54 eq15
    | exact resolve eq15 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq56
  have eq76 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq91 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq65 X1
       grind)
    | exact superpose eq65 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq85
  have eq135 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq91 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq139 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq135 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq143 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq139 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq139 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq139 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq153 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq143 X0 X1
       have j1 := eq76 X1 (σ X0)
       grind)
    | (have r₁ := eq143 X0 X0
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq143 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq143
  have eq160 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq153 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq153
    | (have j0 := eq153 X0 X1
       grind)
    | exact resolve eq153 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq161 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq160 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq167 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq161 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq161
    | exact resolve eq161 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq161 x y
       grind)
    | exact superpose eq161 eq16
    | exact resolve eq16 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq224 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq167 X0 (τ X1)
       grind)
    | exact superpose eq167 eq18
    | exact resolve eq18 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq167
  have eq237 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq224 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq224
    | exact resolve eq224 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq243 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq237 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq237
    | exact resolve eq237 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq263 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq178
       have i₂ := eq243 x y
       grind)
    | exact superpose eq243 eq178
    | exact resolve eq178 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq243
  have eq264 : False := by grind
  exact eq264

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation3058 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  clear eq22
  have eq266 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq266 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq269 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq267 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq267 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq267 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq280 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq269 (σ X0)
       grind)
    | exact superpose eq269 eq15
    | exact resolve eq15 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq269 (τ X0)
       grind)
    | exact superpose eq269 eq31
    | exact resolve eq31 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq293 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq286 X0
       have i₂ := eq269 X0
       grind)
    | exact superpose eq269 eq286
    | exact resolve eq286 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq299 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq280 X0
       have i₂ := eq269 X0
       grind)
    | exact superpose eq269 eq280
    | exact resolve eq280 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq280
  have eq342 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq299 X0
       grind)
    | exact superpose eq299 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq299 X0
       grind)
    | exact superpose eq299 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq346 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq342 X0 X1
       have j1 := eq343 X0 X1
       grind)
    | (have r₁ := eq342 X0 X1
       have r₂ := eq343 X0 X1
       grind)
    | exact resolve eq342 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq343
  have eq357 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op (τ X0) X1) = X1 ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (τ X0)
       have i₂ := eq293 X0
       grind)
    | exact superpose eq293 eq14
    | (have j0 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq14 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq293 X0
       grind)
    | exact superpose eq293 eq12
    | (have j0 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq12 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq361 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq357 X0 X1
       have j1 := eq358 X0 X1
       grind)
    | (have r₁ := eq357 X0 X1
       have r₂ := eq358 X0 X1
       grind)
    | exact resolve eq357 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq358
  have eq400 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq346 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq346
    | exact resolve eq346 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq404 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq346 x (σ y)
       grind)
    | exact superpose eq346 eq16
    | (have j1 := eq346 x (σ y)
       grind)
    | exact resolve eq16 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq415 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq404
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq404
    | exact resolve eq404 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq423 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq400 X1 X0
       grind)
    | exact superpose eq400 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq400 X1 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq400 X0 X1
       grind)
    | exact resolve eq13 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq433 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq423 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq436 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq433 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq433 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq433 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq450 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq436 X1 (τ X0)
       grind)
    | exact superpose eq436 eq18
    | (have j1 := eq436 X1 (τ X0)
       grind)
    | exact resolve eq18 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq467 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq436 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1101 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq450 X1 (τ X0)
       grind)
    | exact superpose eq450 eq17
    | (have j1 := eq450 X1 (τ X0)
       grind)
    | exact resolve eq17 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq450
  have eq1108 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1101 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1101
    | (have j0 := eq1101 X0 X1
       grind)
    | exact resolve eq1101 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101
  have eq1119 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1108 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1108
    | (have j0 := eq1108 X0 X1
       grind)
    | exact resolve eq1108 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108
  have eq1120 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X1) (τ X0))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1119 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1119
    | (have j0 := eq1119 X0 X1
       grind)
    | exact resolve eq1119 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119
  have eq1173 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1120 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1120
    | (have j0 := eq1120 X1 (σ X0)
       grind)
    | exact resolve eq1120 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq1657 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1173 X0 X0
       have i₂ := eq436 X0 (σ X0)
       grind)
    | exact superpose eq436 eq1173
    | (have j0 := eq1173 X0 X1
       have j1 := eq436 X1 (σ X0)
       grind)
    | exact resolve eq1173 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436 eq1173
  have eq1695 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1657 X0 X1
       have j1 := eq467 X1 (σ X0)
       grind)
    | (have r₁ := eq1657 X0 X0
       have r₂ := eq467 X0 (σ X0)
       grind)
    | exact resolve eq1657 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467 eq1657
  have eq1999 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq1695 X1 (σ X0)
       grind)
    | exact superpose eq1695 eq28
    | (have j1 := eq1695 X1 (σ X0)
       grind)
    | exact resolve eq28 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1695
  have eq2010 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1999 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1999
    | (have j0 := eq1999 X0 X1
       grind)
    | exact resolve eq1999 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1999
  have eq2025 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2010 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2010
    | (have j0 := eq2010 X0 X1
       grind)
    | exact resolve eq2010 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2010
  have eq2034 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2025 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2025
    | (have j0 := eq2025 X0 X1
       grind)
    | exact resolve eq2025 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2025
  have eq2126 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2034 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2034
    | (have j0 := eq2034 X1 (τ X0)
       grind)
    | exact resolve eq2034 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2147 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2034 y x
       grind)
    | exact superpose eq2034 eq16
    | (have j1 := eq2034 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq2034 y x
       grind)
    | exact resolve eq16 eq2034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2034
  have eq2180 : y = (k y x) := by grind
  clear eq2147
  have eq2473 : ∀ X0 X1 : G, (M.op (τ X1) X0) = X0 ∨ (M.op (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq361 X1 X0
       have i₂ := eq2126 X1 X0
       grind)
    | exact superpose eq2126 eq361
    | (have j0 := eq361 X1 X0
       have j1 := eq2126 X1 X0
       grind)
    | exact resolve eq361 eq2126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361 eq2126
  have eq2487 : ∀ X0 X1 : G, (M.op (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2473 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2473
  have eq2563 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2487 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2487
    | exact resolve eq2487 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2487
  have eq2704 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2563 x y
       grind)
    | exact superpose eq2563 eq16
    | (have j1 := eq2563 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2563 x y
       grind)
    | exact resolve eq16 eq2563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2563
  have eq2743 : y = (M.op x y) := by grind
  clear eq2704
  have eq2836 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq415
       have i₂ := eq2743
       grind)
    | exact superpose eq2743 eq415
    | exact resolve eq415 eq2743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq2841 : (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq2836
  have eq2844 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2841
       have i₂ := eq2180
       grind)
    | exact superpose eq2180 eq2841
    | exact resolve eq2841 eq2180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2180 eq2841
  have eq2849 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2844
       grind)
    | exact superpose eq2844 eq16
    | exact resolve eq16 eq2844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2844
  have eq2866 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2849
       have i₂ := eq2743
       grind)
    | exact superpose eq2743 eq2849
    | exact resolve eq2849 eq2743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2743 eq2849
  have eq2867 : False := by grind
  exact eq2867

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation3058 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq62 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq74 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq65 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq75 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq74 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq90 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq75 (σ X0)
       grind)
    | exact superpose eq75 eq15
    | exact resolve eq15 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq90 X0
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq90
    | exact resolve eq90 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq90
  have eq117 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq169 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq160 X0 X1
       have i₂ := eq101 X1
       grind)
    | exact superpose eq101 eq160
    | (have j0 := eq160 X0 X1
       grind)
    | exact resolve eq160 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq624 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq169 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq169
    | (have j0 := eq169 (M.op X1 X1) X1
       grind)
    | exact resolve eq169 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq637 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq624 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq624
    | (have j0 := eq624 (σ (M.op X1 X1)) X1
       grind)
    | exact resolve eq624 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq624
  have eq639 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq637 X0 X1
       have j1 := eq117 X1 X0
       grind)
    | (have r₁ := eq637 X0 X0
       have r₂ := eq117 X0 X1
       grind)
    | (have r₁ := eq637 (σ (M.op X0 X0)) X0
       have r₂ := eq117 X0 X1
       grind)
    | (have r₁ := eq637 (σ X0) (M.op X0 X0)
       have r₂ := eq117 X0 X1
       grind)
    | exact resolve eq637 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq637
  have eq641 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq639 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq639
    | exact resolve eq639 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq639 (σ X0) X1
       grind)
    | exact superpose eq639 eq15
    | (have j1 := eq639 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq681 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq641 (τ X1) X0
       grind)
    | exact superpose eq641 eq19
    | (have j1 := eq641 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq641
  have eq765 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq681 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq681
    | exact resolve eq681 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq813 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq765 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq765
    | (have j0 := eq765 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq765 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq960 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq652 x y
       grind)
    | exact superpose eq652 eq16
    | (have j1 := eq652 x y
       grind)
    | exact resolve eq16 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq974 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq960
       have i₂ := eq813 y x
       grind)
    | exact superpose eq813 eq960
    | (have j1 := eq813 (σ x) (σ y)
       grind)
    | (have r₁ := eq960
       have r₂ := eq813 y x
       grind)
    | (have r₁ := eq960
       have r₂ := eq813 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq960
       have r₂ := eq813 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq960 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813 eq960
  have eq975 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq974
  have eq978 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq975
       grind)
    | exact superpose eq975 eq16
    | exact resolve eq16 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975
  have eq979 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq978
       have r₂ := eq101 x
       grind)
    | exact resolve eq978 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978
  have eq980 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq979
       grind)
    | exact superpose eq979 eq16
    | exact resolve eq16 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq981 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq979
       grind)
    | exact superpose eq979 eq10
    | exact resolve eq10 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979
  have eq1027 : x = y := by
    first
    | (have i₁ := eq981
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq981
    | exact resolve eq981 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981
  have eq1028 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq980
       have i₂ := eq101 x
       grind)
    | exact superpose eq101 eq980
    | exact resolve eq980 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq980
  have eq1029 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1028
       have i₂ := eq1027
       grind)
    | exact superpose eq1027 eq1028
    | exact resolve eq1028 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027 eq1028
  have eq1030 : False := by grind
  exact eq1030

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation3058 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3058 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq449 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3242 : ∀ X0 X1 : G, (M.op X0 (σ X1)) ≠ (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq449 X0 X1
       grind)
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq449 X0 X1
       grind)
    | exact superpose eq449 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq449 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq449 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq449 X0 X1
       grind)
    | exact resolve eq13 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq3246 : ∀ X0 X1 : G, (M.op X0 (σ X1)) ≠ (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3242 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3242
  have eq3247 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3246 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3246
  have eq4729 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq3247 X0 X1
       grind)
    | exact superpose eq3247 eq28
    | (have j1 := eq3247 X0 X1
       grind)
    | exact resolve eq28 eq3247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3247
  have eq4766 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq4729 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4729
  have eq4782 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4766 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4766
    | exact resolve eq4766 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4766
  have eq4898 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4782 X0 X1
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq4782
    | (have j0 := eq4782 (τ (k X1 X0)) (τ (M.op X1 X0))
       grind)
    | exact resolve eq4782 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq4782
  have eq4933 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq4898 X1 X0
       grind)
    | exact superpose eq4898 eq11
    | (have j1 := eq4898 (k X0 X1) (σ (τ (M.op X0 X1)))
       grind)
    | exact resolve eq11 eq4898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4898
  have eq5055 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4933 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq4933
    | (have j0 := eq4933 (k X0 X1) (M.op X0 X1)
       grind)
    | exact resolve eq4933 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4933
  have eq5086 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq5055 X0 (τ X1)
       grind)
    | exact superpose eq5055 eq19
    | (have j1 := eq5055 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq5055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq5108 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq5055 (σ X0) (σ X1)
       grind)
    | exact superpose eq5055 eq15
    | (have j1 := eq5055 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq5055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5055
  have eq5349 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5086 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5086
    | exact resolve eq5086 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5086
  have eq5425 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5349 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5349
    | (have j0 := eq5349 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq5349 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5349
  have eq5812 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5108 x y
       grind)
    | exact superpose eq5108 eq16
    | (have j1 := eq5108 x y
       grind)
    | exact resolve eq16 eq5108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5108
  have eq5849 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5812
       have i₂ := eq5425 y x
       grind)
    | exact superpose eq5425 eq5812
    | (have j1 := eq5425 (σ x) (σ y)
       grind)
    | (have r₁ := eq5812
       have r₂ := eq5425 y x
       grind)
    | (have r₁ := eq5812
       have r₂ := eq5425 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5812
       have r₂ := eq5425 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5812 eq5425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5425 eq5812
  have eq5852 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq5849
  have eq5856 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5852
       grind)
    | exact superpose eq5852 eq16
    | exact resolve eq16 eq5852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5852
  have eq5857 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq5856
       have r₂ := eq22 x
       grind)
    | exact resolve eq5856 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5856
  have eq5858 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5857
       grind)
    | exact superpose eq5857 eq16
    | exact resolve eq16 eq5857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5859 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5857
       grind)
    | exact superpose eq5857 eq10
    | exact resolve eq10 eq5857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5857
  have eq5916 : x = y := by
    first
    | (have i₁ := eq5859
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5859
    | exact resolve eq5859 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5859
  have eq5917 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5858
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5858
    | exact resolve eq5858 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5858
  have eq5918 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5917
       have i₂ := eq5916
       grind)
    | exact superpose eq5916 eq5917
    | exact resolve eq5917 eq5916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5916 eq5917
  have eq5919 : False := by grind
  exact eq5919

/-- `Equation3071`: `x = (((x ◇ y) ◇ x) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_x_pxy_pyx_Equation3071 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3071 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3071.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
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
  clear eq18
  have eq62 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
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
  have eq68 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X1)
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq12
    | (have j0 := eq12 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X1)
       have r₂ := eq62 X0 X1
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq73 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op (σ X0) X1)
       have i₂ := eq70 (σ X0) X1
       grind)
    | exact superpose eq70 eq28
    | exact resolve eq28 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (k X0 (τ (M.op (σ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq73
    | exact resolve eq73 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq646 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) X0) = X0 ∨ (M.op (M.op X0 X1) X0) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X0
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq13
    | (have j0 := eq13 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X1) X0
       have r₂ := eq62 X0 X1
       grind)
    | exact resolve eq13 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq647 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k (M.op X0 X1) X0) ∨ (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq646 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq658 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq675 : ∀ X0 X1 : G, (M.op (τ (M.op (σ X0) X1)) X0) = X0 ∨ (M.op (τ (M.op (σ X0) X1)) X0) = X0 ∨ (τ (M.op (σ X0) X1)) = (M.op X0 (τ (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 X1
       have i₂ := eq14 X0 (τ (M.op (σ X0) X1))
       grind)
    | exact superpose eq14 eq76
    | (have j1 := eq14 X0 (τ (M.op (σ X0) X1))
       grind)
    | exact resolve eq76 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq698 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (M.op X0 (τ (M.op (σ X0) X1))) ∨ (M.op (τ (M.op (σ X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq675 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq729 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq658 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq658
    | (have j0 := eq658 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq658 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq730 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (σ (M.op X0 X1)) = (M.op (σ X0) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq658 X0 (M.op X0 X1)
       have i₂ := eq70 X0 X1
       grind)
    | exact superpose eq70 eq658
    | (have j0 := eq658 X0 (M.op X0 X1)
       grind)
    | exact resolve eq658 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq776 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ (M.op X0 X1))) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq730 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq6574 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (M.op (σ (M.op X0 X1)) (σ X0)) = (k (σ (M.op X0 X1)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ (M.op X0 X1)) (σ X0)
       have i₂ := eq776 X0 X1
       grind)
    | exact superpose eq776 eq13
    | (have j0 := eq13 (σ (M.op X0 X1)) (σ X0)
       have j1 := eq776 X0 X1
       grind)
    | (have r₁ := eq13 (σ (M.op X0 X1)) (σ X0)
       have r₂ := eq776 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ (M.op X0 X1))
       have r₂ := eq776 X0 X1
       grind)
    | exact resolve eq13 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq6582 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (M.op (σ (M.op X0 X1)) (σ X0)) = (k (σ (M.op X0 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq6574 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6574
  have eq6583 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (M.op (σ (M.op X0 X1)) (σ X0)) = (k (σ (M.op X0 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq6582 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6582
  have eq6587 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X1)) (σ X0)) = (σ (k (M.op X0 X1) X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6583 X0 X1
       have i₂ := eq15 (M.op X0 X1) X0
       grind)
    | exact superpose eq15 eq6583
    | (have j0 := eq6583 X0 X1
       grind)
    | exact resolve eq6583 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6583
  have eq6596 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ X0) (τ (M.op X0 X1))) ∨ (τ X0) = (M.op (τ (M.op X0 X1)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq698 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq698
    | exact resolve eq698 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8302 : ∀ X0 X1 : G, (k X1 (k X0 (τ (σ X1)))) = X1 ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X1 (σ X0)
       have i₂ := eq682 (σ X1) X0
       grind)
    | exact superpose eq682 eq76
    | (have j1 := eq682 (σ X1) X0
       grind)
    | exact resolve eq76 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq8362 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k X1 (k X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8302 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq8302
    | (have j0 := eq8302 X1 X0
       grind)
    | exact resolve eq8302 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8302
  have eq21229 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq729 x y
       grind)
    | exact superpose eq729 eq16
    | (have j1 := eq729 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq729 x y
       grind)
    | exact resolve eq16 eq729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq21284 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq21229
  have eq21330 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X1)) (σ X0)) = (σ (k (M.op X0 X1) X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq6587 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6587
  have eq41517 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (k y (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8362 x y
       grind)
    | exact superpose eq8362 eq16
    | (have j1 := eq8362 x y
       grind)
    | exact resolve eq16 eq8362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8362
  have eq75015 : x = (k x (τ (σ y))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq76 x (σ y)
       have i₂ := eq21284
       grind)
    | exact superpose eq21284 eq76
    | exact resolve eq76 eq21284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21284
  have eq75095 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq75015
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq75015
    | exact resolve eq75015 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75015
  have eq75122 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq75095
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq75095
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq75095
       have r₂ := eq12 y x
       grind)
    | exact resolve eq75095 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75095
  have eq75150 : (τ (σ x)) = (M.op y (τ (σ x))) ∨ y = (M.op (τ (σ x)) y) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq698 y (σ x)
       have i₂ := eq75122
       grind)
    | exact superpose eq75122 eq698
    | exact resolve eq698 eq75122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698 eq75122
  have eq75225 : x = (M.op y x) ∨ y = (M.op (τ (σ x)) y) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq75150
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq75150
    | exact resolve eq75150 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75150
  have eq75226 : x = (M.op y x) ∨ y = (M.op (τ (σ x)) y) ∨ x = (k x y) := by grind
  clear eq75225
  have eq75248 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq75226
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq75226
    | exact resolve eq75226 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75226
  have eq75261 : x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq75248
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq75248
       have r₂ := eq12 y x
       grind)
    | exact resolve eq75248 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75248
  have eq75289 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq75261
       grind)
    | exact superpose eq75261 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq75261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75295 : y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq75289
  have eq75299 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (k y (k x y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq41517
       have i₂ := eq75295
       grind)
    | exact superpose eq75295 eq41517
    | exact resolve eq41517 eq75295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41517
  have eq75300 : ∀ X0 : G, x = (M.op (M.op (M.op y x) X0) x) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq75295
       grind)
    | exact superpose eq75295 eq9
    | exact resolve eq9 eq75295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75307 : (M.op y x) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq647 x y
       have i₂ := eq75295
       grind)
    | exact superpose eq75295 eq647
    | exact resolve eq647 eq75295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75295
  have eq75336 : (M.op y x) = (k y x) ∨ x = (M.op y x) := by grind
  clear eq75307
  have eq75340 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (k y (k x y)) ∨ x = (M.op y x) := by grind
  clear eq75299
  have eq75342 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (k y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq75261 eq75340
    | exact resolve eq75340 eq75261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75261 eq75340
  have eq75343 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq75342
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq75342
       have r₂ := eq12 y x
       grind)
    | exact resolve eq75342 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75342
  have eq75720 : y = (k y (τ (σ x))) ∨ y = (k y x) := by
    first
    | (have i₁ := eq76 y (σ x)
       have i₂ := eq75343
       grind)
    | exact superpose eq75343 eq76
    | exact resolve eq76 eq75343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75343
  have eq75796 : y = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq75720
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq75720
    | exact resolve eq75720 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75720
  have eq75797 : y = (k y x) := by grind
  clear eq75796
  have eq75847 : y = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq75336
       have i₂ := eq75797
       grind)
    | exact superpose eq75797 eq75336
    | exact resolve eq75336 eq75797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75336
  have eq75850 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq658 y x
       have i₂ := eq75797
       grind)
    | exact superpose eq75797 eq658
    | (have j0 := eq658 y x
       grind)
    | exact resolve eq658 eq75797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq75797
  have eq75854 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq75850
  have eq75894 : x ≠ y ∨ x = (M.op y x) := by grind
  have eq76485 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq75847 eq75300
    | exact resolve eq75300 eq75847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75300
  have eq76486 : x = (M.op y x) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq76485 x
       have i₂ := eq75847
       grind)
    | exact superpose eq75847 eq76485
    | exact resolve eq76485 eq75847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75847 eq76485
  have eq76547 : x = (M.op y x) ∨ x = y := by grind
  clear eq76486
  have eq76562 : x = (M.op y x) := by
    first
    | (have r₁ := eq76547
       have r₂ := eq75894
       grind)
    | exact resolve eq76547 eq75894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75894 eq76547
  have eq76584 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq76562
       grind)
    | exact superpose eq76562 eq9
    | exact resolve eq9 eq76562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76591 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq647 y x
       have i₂ := eq76562
       grind)
    | exact superpose eq76562 eq647
    | exact resolve eq647 eq76562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq76614 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21330 y x
       have i₂ := eq76562
       grind)
    | exact superpose eq76562 eq21330
    | exact resolve eq21330 eq76562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21330 eq76562
  have eq84082 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq76614
       have i₂ := eq76591
       grind)
    | exact superpose eq76591 eq76614
    | exact resolve eq76614 eq76591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84237 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq84082
       have r₂ := eq16
       grind)
    | exact resolve eq84082 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84082
  have eq84240 : x = (k x (τ (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq76 x (σ y)
       have i₂ := eq84237
       grind)
    | exact superpose eq84237 eq76
    | exact resolve eq76 eq84237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq84237
  have eq84319 : x = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq84240
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq84240
    | exact resolve eq84240 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84240
  have eq84341 : x = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq84319
       have r₂ := eq12 x y
       grind)
    | exact resolve eq84319 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84319
  have eq84367 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq76591
       have i₂ := eq84341
       grind)
    | exact superpose eq84341 eq76591
    | exact resolve eq76591 eq84341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76591
  have eq84368 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq76614
       have i₂ := eq84341
       grind)
    | exact superpose eq84341 eq76614
    | exact resolve eq76614 eq84341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76614 eq84341
  have eq85518 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq84368
       grind)
    | exact superpose eq84368 eq16
    | exact resolve eq16 eq84368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85632 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq85518
       have i₂ := eq84367
       grind)
    | exact superpose eq84367 eq85518
    | exact resolve eq85518 eq84367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84367 eq85518
  have eq85633 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq85632
  have eq85688 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6596 (σ x) (σ y)
       have i₂ := eq85633
       grind)
    | exact superpose eq85633 eq6596
    | exact resolve eq6596 eq85633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6596 eq85633
  have eq85709 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) := by grind
  clear eq85688
  have eq85721 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq85709
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq85709
    | exact resolve eq85709 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85709
  have eq85765 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq62 x y
       have i₂ := eq85721
       grind)
    | exact superpose eq85721 eq62
    | exact resolve eq62 eq85721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85721
  have eq85804 : x = (M.op x x) := by grind
  clear eq85765
  have eq85816 : ∀ X0 : G, x = (M.op (M.op (M.op x x) X0) x) := by
    intro X0
    first
    | (have i₁ := eq9 x x X0
       have i₂ := eq85804
       grind)
    | exact superpose eq85804 eq9
    | exact resolve eq9 eq85804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85877 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq85816 X0
       have i₂ := eq85804
       grind)
    | exact superpose eq85804 eq85816
    | exact resolve eq85816 eq85804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85804 eq85816
  have eq85958 : y = (M.op x y) := by
    first
    | (have i₁ := eq76584 x
       have i₂ := eq85877 y
       grind)
    | exact superpose eq85877 eq76584
    | exact resolve eq76584 eq85877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76584 eq85877
  have eq87134 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq85958
       grind)
    | exact superpose eq85958 eq16
    | exact resolve eq16 eq85958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85958
  have eq87434 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq87134
       have i₂ := eq84368
       grind)
    | exact superpose eq84368 eq87134
    | (have r₁ := eq87134
       have r₂ := eq84368
       grind)
    | exact resolve eq87134 eq84368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84368
  have eq87435 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq87134
       have i₂ := eq75854
       grind)
    | exact superpose eq75854 eq87134
    | (have r₁ := eq87134
       have r₂ := eq75854
       grind)
    | exact resolve eq87134 eq75854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75854
  have eq87445 : (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq87435
  have eq87446 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq87434
  have eq87476 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) (σ x) X0
       have i₂ := eq87445
       grind)
    | exact superpose eq87445 eq9
    | exact resolve eq9 eq87445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87445
  have eq87563 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq87134
       have i₂ := eq87446
       grind)
    | exact superpose eq87446 eq87134
    | exact resolve eq87134 eq87446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87134
  have eq87593 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq62 (σ x) (σ y)
       have i₂ := eq87446
       grind)
    | exact superpose eq87446 eq62
    | exact resolve eq62 eq87446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq91357 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq87476 X0
       have i₂ := eq87446
       grind)
    | exact superpose eq87446 eq87476
    | exact resolve eq87476 eq87446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87476
  have eq92826 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq91357 (σ x)
       have i₂ := eq87593
       grind)
    | exact superpose eq87593 eq91357
    | exact resolve eq91357 eq87593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87593 eq91357
  have eq92919 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq92826
       have i₂ := eq87446
       grind)
    | exact superpose eq87446 eq92826
    | exact resolve eq92826 eq87446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87446 eq92826
  have eq92937 : False := by grind
  exact eq92937

/-- `Equation3071`: `x = (((x ◇ y) ◇ x) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_y_pyx_pxy_Equation3071 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3071 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3071.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq40 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 (k (τ X0) X1) X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq28
    | exact resolve eq28 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq28
  have eq62 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
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
  have eq68 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq12
    | (have j0 := eq12 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq12 (M.op X0 X1) X0
       have r₂ := eq62 X0 X1
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (k (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq73 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) X1)
       have i₂ := eq70 (τ X0) X1
       grind)
    | exact superpose eq70 eq18
    | exact resolve eq18 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op (σ X0) X1) X0
       have i₂ := eq70 (σ X0) X1
       grind)
    | exact superpose eq70 eq22
    | exact resolve eq22 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq74
    | exact resolve eq74 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq76 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq73
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq209 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X0 X1) X0) X2) = (M.op X0 (M.op (M.op (M.op X0 X1) X0) X2)) ∨ (M.op X0 (M.op (M.op (M.op X0 X1) X0) X2)) = (k (M.op (M.op (M.op X0 X1) X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op (M.op X0 X1) X0) X2) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op (M.op (M.op X0 X1) X0) X2) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op (M.op X0 X1) X0) X2) X0
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) X0) = X0 ∨ (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 X1)
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq13
    | (have j0 := eq13 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X1)
       have r₂ := eq62 X0 X1
       grind)
    | exact resolve eq13 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) ∨ (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq210 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq212 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X0 X1) X0) X2)) = (k (M.op (M.op (M.op X0 X1) X0) X2) X0) ∨ (M.op (M.op (M.op X0 X1) X0) X2) = (M.op X0 (M.op (M.op (M.op X0 X1) X0) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq209 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq650 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq664 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq22
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq22 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 (τ X1)) ∨ (M.op (τ X1) X0) = X0 := by
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
  clear eq18
  have eq675 : ∀ X0 X1 : G, (M.op (σ (M.op (τ X0) X1)) X0) = X0 ∨ (M.op (σ (M.op (τ X0) X1)) X0) = X0 ∨ (σ (M.op (τ X0) X1)) = (M.op X0 (σ (M.op (τ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 X1
       have i₂ := eq14 (σ (M.op (τ X0) X1)) X0
       grind)
    | exact superpose eq14 eq76
    | (have j1 := eq14 (σ (M.op (τ X0) X1)) X0
       grind)
    | exact resolve eq76 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq687 : ∀ X0 X1 : G, (M.op (τ (M.op (σ X0) X1)) X0) = X0 ∨ (M.op (τ (M.op (σ X0) X1)) X0) = X0 ∨ (τ (M.op (σ X0) X1)) = (M.op X0 (τ (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X1
       have i₂ := eq14 (τ (M.op (σ X0) X1)) X0
       grind)
    | exact superpose eq14 eq75
    | (have j1 := eq14 (τ (M.op (σ X0) X1)) X0
       grind)
    | exact resolve eq75 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (M.op X0 (τ (M.op (σ X0) X1))) ∨ (M.op (τ (M.op (σ X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq687 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq702 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = (M.op X0 (σ (M.op (τ X0) X1))) ∨ (M.op (σ (M.op (τ X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq675 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq3754 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq650 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq650
    | (have j0 := eq650 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq650 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3757 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (σ (M.op X0 X1)) = (M.op (σ X0) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq650 (M.op X0 X1) X0
       have i₂ := eq70 X0 X1
       grind)
    | exact superpose eq70 eq650
    | (have j0 := eq650 (M.op X0 X1) X0
       grind)
    | exact resolve eq650 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3867 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ (M.op X0 X1))) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3757 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3757
  have eq6574 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (M.op (σ (M.op X0 X1)) (σ X0)) = (k (σ X0) (σ (M.op X0 X1))) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ (M.op X0 X1))
       have i₂ := eq3867 X0 X1
       grind)
    | exact superpose eq3867 eq13
    | (have j0 := eq13 (σ X0) (σ (M.op X0 X1))
       have j1 := eq3867 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ (M.op X0 X1))
       have r₂ := eq3867 X0 X1
       grind)
    | (have r₁ := eq13 (σ (M.op X0 X1)) (σ X0)
       have r₂ := eq3867 X0 X1
       grind)
    | exact resolve eq13 eq3867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3867
  have eq6582 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (M.op (σ (M.op X0 X1)) (σ X0)) = (k (σ X0) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq6574 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6574
  have eq6583 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (M.op (σ (M.op X0 X1)) (σ X0)) = (k (σ X0) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq6582 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6582
  have eq6587 : ∀ X0 X1 : G, (σ (k X0 (M.op X0 X1))) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6583 X0 X1
       have i₂ := eq15 X0 (M.op X0 X1)
       grind)
    | exact superpose eq15 eq6583
    | (have j0 := eq6583 X0 X1
       grind)
    | exact resolve eq6583 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6583
  have eq6596 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ X0) (τ (M.op X0 X1))) ∨ (τ X0) = (M.op (τ (M.op X0 X1)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq698 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq698
    | exact resolve eq698 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6700 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ (M.op (τ X0) X1)) X0) X2) X0) = X0 ∨ (M.op (σ (M.op (τ X0) X1)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 (σ (M.op (τ X0) X1)) X2
       have i₂ := eq702 X0 X1
       grind)
    | exact superpose eq702 eq9
    | (have j1 := eq702 X0 X1
       grind)
    | exact resolve eq9 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6934 : ∀ X0 X1 : G, (k (k (σ (τ X0)) X1) X0) = X0 ∨ (τ X1) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (τ X1)
       have i₂ := eq669 (τ X0) X1
       grind)
    | exact superpose eq669 eq76
    | (have j1 := eq669 (τ X0) X1
       grind)
    | exact resolve eq76 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq7036 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X0) (τ X1)) ∨ (k (k X0 X1) X0) = X0 ∨ (τ X0) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6934 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6934
    | (have j0 := eq6934 X0 X1
       grind)
    | exact resolve eq6934 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6934
  have eq7877 : ∀ X0 X1 : G, (k (k (τ (σ X0)) X1) X0) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 (σ X1)
       have i₂ := eq664 (σ X0) X1
       grind)
    | exact superpose eq664 eq75
    | (have j1 := eq664 (σ X0) X1
       grind)
    | exact resolve eq75 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq7934 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (k X0 X1) X0) = X0 ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7877 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7877
    | (have j0 := eq7877 X0 X1
       grind)
    | exact resolve eq7877 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7877
  have eq8552 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = X1 ∨ (k (k X1 X0) X1) = X1 ∨ (τ X1) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X1 (τ X0)
       have i₂ := eq7036 X1 X0
       grind)
    | exact superpose eq7036 eq76
    | (have j1 := eq7036 X1 X0
       grind)
    | exact resolve eq76 eq7036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7036
  have eq8595 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X0) (τ X1)) ∨ (k (k X1 X0) X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8552 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8552
    | (have j0 := eq8552 X0 X1
       grind)
    | exact resolve eq8552 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8552
  have eq12089 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 (σ (τ X0))) ∨ (M.op (σ (τ X0)) X1) = X1 ∨ (k (k X0 X1) X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq702 X0 (τ X1)
       have i₂ := eq8595 X0 X1
       grind)
    | exact superpose eq8595 eq702
    | (have j1 := eq8595 X1 X0
       grind)
    | exact resolve eq702 eq8595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq12091 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ (τ X0)) X1) X2) X1) = X1 ∨ (M.op (σ (τ X0)) X1) = X1 ∨ (k (k X0 X1) X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6700 X0 (τ X1) X2
       have i₂ := eq8595 X0 X1
       grind)
    | exact superpose eq8595 eq6700
    | (have j1 := eq8595 X1 X0
       grind)
    | exact resolve eq6700 eq8595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6700 eq8595
  have eq12145 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) X1) = X1 ∨ (M.op (σ (τ X0)) X1) = X1 ∨ (k (k X0 X1) X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12091 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12091
    | (have j0 := eq12091 X0 X1 X2
       grind)
    | exact resolve eq12091 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12091
  have eq12146 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op (σ (τ X0)) X1) = X1 ∨ (k (k X0 X1) X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12089 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12089
    | (have j0 := eq12089 X0 X1
       grind)
    | exact resolve eq12089 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12089
  have eq12154 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X1 ∨ (M.op (M.op (M.op X0 X1) X2) X1) = X1 ∨ (k (k X0 X1) X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12145 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12145
    | (have j0 := eq12145 X0 X1 X2
       grind)
    | exact resolve eq12145 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12145
  have eq12155 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k (k X0 X1) X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12146 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12146
    | (have j0 := eq12146 X0 X1
       grind)
    | exact resolve eq12146 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12146
  have eq12159 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) X1) = X1 ∨ (k (k X0 X1) X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq12154 X0 X1 X2
       have j1 := eq12 (k X0 X1) X0
       grind)
    | (have r₁ := eq12154 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq12154 X0 X0 X2
       have r₂ := eq12 X0 (M.op (M.op X0 X0) X2)
       grind)
    | exact resolve eq12154 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12154
  have eq12160 : ∀ X0 X1 : G, (k (k X0 X1) X0) = X0 ∨ (M.op X1 X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12155 X0 X1
       have j1 := eq12 (k X0 X1) X0
       grind)
    | (have r₁ := eq12155 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq12155 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq12155 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12155
  have eq21337 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (k (k X1 X0) X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq212 x X1 X1
       have i₂ := eq12159 x X1 x
       grind)
    | exact superpose eq12159 eq212
    | (have j1 := eq12159 X1 X0 x
       grind)
    | exact resolve eq212 eq12159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq12159
  have eq21374 : ∀ X0 X1 : G, (k (k X1 X0) X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq21337 X0 X1
       have j1 := eq12 (k X1 X0) X1
       grind)
    | (have r₁ := eq21337 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq21337 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21337
  have eq21395 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op X0 X1)) ∨ (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21374 X0 (M.op X0 X1)
       have i₂ := eq70 X0 X1
       grind)
    | exact superpose eq70 eq21374
    | (have j0 := eq21374 X0 (M.op X0 X1)
       grind)
    | exact resolve eq21374 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq21579 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq21395 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21395
  have eq41276 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3754 x y
       grind)
    | exact superpose eq3754 eq16
    | (have j1 := eq3754 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq3754 x y
       grind)
    | exact resolve eq16 eq3754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3754
  have eq41339 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq41276
  have eq41395 : ∀ X0 X1 : G, (σ (k X0 (M.op X0 X1))) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq6587 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6587
  have eq42898 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (k (k X1 X0) X1) = X1 ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X1 (σ X0)
       have i₂ := eq7934 X1 X0
       grind)
    | exact superpose eq7934 eq75
    | (have j1 := eq7934 X1 X0
       grind)
    | exact resolve eq75 eq7934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7934
  have eq42987 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (k X1 X0) X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42898 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq42898
    | (have j0 := eq42898 X0 X1
       grind)
    | exact resolve eq42898 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42898
  have eq43046 : ∀ X0 X1 : G, (M.op (σ X1) X0) = X0 ∨ (τ X0) = (k (k (τ X0) X1) (τ X0)) ∨ (τ X0) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq42987 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq42987
    | (have j0 := eq42987 X1 (τ X0)
       grind)
    | exact resolve eq42987 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43064 : (σ (M.op x y)) ≠ (σ y) ∨ y = (k (k y x) y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq42987 x y
       grind)
    | exact superpose eq42987 eq16
    | (have j1 := eq42987 x y
       grind)
    | exact resolve eq16 eq42987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42987
  have eq43144 : (σ y) ≠ (σ y) ∨ y = (k (k y x) y) ∨ y = (k x y) := by
    first
    | exact superpose eq12160 eq43064
    | (have j1 := eq12160 y x
       grind)
    | exact resolve eq43064 eq12160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12160 eq43064
  have eq43145 : y = (k (k y x) y) ∨ y = (k x y) := by grind
  clear eq43144
  have eq43149 : ∀ X0 X1 : G, (τ X0) = (τ (k (k X0 (σ X1)) X0)) ∨ (M.op (σ X1) X0) = X0 ∨ (τ X0) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq43046 X0 X1
       have i₂ := eq40 X0 X1 X0
       grind)
    | exact superpose eq40 eq43046
    | (have j0 := eq43046 X0 X1
       grind)
    | exact resolve eq43046 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq43046
  have eq56672 : ∀ X0 X1 : G, (τ (σ (M.op (τ (σ X0)) X1))) = (τ (k (σ X0) (σ (M.op (τ (σ X0)) X1)))) ∨ (σ (M.op (τ (σ X0)) X1)) = (M.op (σ X0) (σ (M.op (τ (σ X0)) X1))) ∨ (τ (σ (M.op (τ (σ X0)) X1))) = (k X0 (τ (σ (M.op (τ (σ X0)) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq43149 (σ (M.op (τ (σ X0)) X1)) X0
       have i₂ := eq76 (σ X0) X1
       grind)
    | exact superpose eq76 eq43149
    | (have j0 := eq43149 (σ (M.op (τ (σ X0)) X1)) X0
       grind)
    | exact resolve eq43149 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq43149
  have eq57005 : ∀ X0 X1 : G, (τ (σ (M.op (τ (σ X0)) X1))) = (k (τ (σ X0)) (M.op (τ (σ X0)) X1)) ∨ (σ (M.op (τ (σ X0)) X1)) = (M.op (σ X0) (σ (M.op (τ (σ X0)) X1))) ∨ (τ (σ (M.op (τ (σ X0)) X1))) = (k X0 (τ (σ (M.op (τ (σ X0)) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq56672 X0 X1
       have i₂ := eq22 (σ X0) (M.op (τ (σ X0)) X1)
       grind)
    | exact superpose eq22 eq56672
    | (have j0 := eq56672 X0 X1
       grind)
    | exact resolve eq56672 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq56672
  have eq57097 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = (τ (σ (M.op X0 X1))) ∨ (σ (M.op (τ (σ X0)) X1)) = (M.op (σ X0) (σ (M.op (τ (σ X0)) X1))) ∨ (τ (σ (M.op (τ (σ X0)) X1))) = (k X0 (τ (σ (M.op (τ (σ X0)) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq57005 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq57005
    | (have j0 := eq57005 X0 X1
       grind)
    | exact resolve eq57005 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57005
  have eq57158 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op X0 X1)) ∨ (σ (M.op (τ (σ X0)) X1)) = (M.op (σ X0) (σ (M.op (τ (σ X0)) X1))) ∨ (τ (σ (M.op (τ (σ X0)) X1))) = (k X0 (τ (σ (M.op (τ (σ X0)) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq57097 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq57097
    | (have j0 := eq57097 X0 X1
       grind)
    | exact resolve eq57097 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57097
  have eq57210 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = (k X0 (M.op X0 X1)) ∨ (τ (σ (M.op (τ (σ X0)) X1))) = (k X0 (τ (σ (M.op (τ (σ X0)) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq57158 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq57158
    | (have j0 := eq57158 X0 X1
       grind)
    | exact resolve eq57158 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57158
  have eq57251 : ∀ X0 X1 : G, (M.op (τ (σ X0)) X1) = (k X0 (M.op (τ (σ X0)) X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ X0) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq57210 X0 X1
       have i₂ := eq10 (M.op (τ (σ X0)) X1)
       grind)
    | exact superpose eq10 eq57210
    | (have j0 := eq57210 X0 X1
       grind)
    | exact resolve eq57210 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57210
  have eq57284 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ X0) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq57251 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq57251
    | (have j0 := eq57251 X0 X1
       grind)
    | exact resolve eq57251 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57251
  have eq57285 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq57284 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57284
  have eq101720 : x = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq75 x (σ y)
       have i₂ := eq41339
       grind)
    | exact superpose eq41339 eq75
    | exact resolve eq75 eq41339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41339
  have eq101782 : x = (k y x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq101720
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq101720
    | exact resolve eq101720 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101720
  have eq101800 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq101782
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq101782
       have r₂ := eq12 y x
       grind)
    | (have r₁ := eq101782
       have r₂ := eq12 x y
       grind)
    | exact resolve eq101782 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101782
  have eq101816 : y = (k (τ (σ x)) y) ∨ x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq75 y (σ x)
       have i₂ := eq101800
       grind)
    | exact superpose eq101800 eq75
    | exact resolve eq75 eq101800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq101817 : (τ (σ x)) = (M.op y (τ (σ x))) ∨ y = (M.op (τ (σ x)) y) ∨ x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq698 y (σ x)
       have i₂ := eq101800
       grind)
    | exact superpose eq101800 eq698
    | exact resolve eq698 eq101800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698 eq101800
  have eq101879 : x = (M.op y x) ∨ y = (M.op (τ (σ x)) y) ∨ x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq101817
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq101817
    | exact resolve eq101817 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101817
  have eq101880 : x = (M.op y x) ∨ y = (M.op (τ (σ x)) y) ∨ x = (k y x) := by grind
  clear eq101879
  have eq101881 : y = (k x y) ∨ x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq101816
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq101816
    | exact resolve eq101816 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101816
  have eq101894 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq101880
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq101880
    | exact resolve eq101880 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101880
  have eq101895 : y = (k x y) ∨ x = (k y x) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq101881
       have r₂ := eq12 x y
       grind)
    | exact resolve eq101881 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101881
  have eq101903 : x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq101894
       have r₂ := eq12 y x
       grind)
    | (have r₁ := eq101894
       have r₂ := eq12 x y
       grind)
    | exact resolve eq101894 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101894
  have eq101910 : y = (k x y) ∨ y = (k x y) := by
    first
    | exact superpose eq101895 eq43145
    | exact resolve eq43145 eq101895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43145
  have eq101921 : x = (k y x) ∨ (M.op x y) = (k y x) ∨ x = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq21374 y x
       have i₂ := eq101895
       grind)
    | exact superpose eq101895 eq21374
    | (have j0 := eq21374 y x
       grind)
    | exact resolve eq21374 eq101895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21374 eq101895
  have eq101924 : (M.op x y) = (k y x) ∨ x = (k y x) := by grind
  clear eq101921
  have eq101930 : y = (k x y) := by grind
  clear eq101910
  have eq101947 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq650 x y
       have i₂ := eq101930
       grind)
    | exact superpose eq101930 eq650
    | (have j0 := eq650 x y
       grind)
    | exact resolve eq650 eq101930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq101956 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq101947
  have eq101959 : x = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq101903
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq101903
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq101903 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101903
  have eq101972 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq101959
  have eq101973 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq101956
  have eq102119 : y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq101972
  have eq102140 : ∀ X0 : G, x = (M.op (M.op (M.op y x) X0) x) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq102119
       grind)
    | exact superpose eq102119 eq9
    | exact resolve eq9 eq102119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102147 : (k x y) = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq211 x y
       have i₂ := eq102119
       grind)
    | exact superpose eq102119 eq211
    | exact resolve eq211 eq102119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102119
  have eq102175 : (k x y) = (M.op y x) ∨ x = (M.op y x) := by grind
  clear eq102147
  have eq102180 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq101973
  have eq102181 : y = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq102175
       have i₂ := eq101930
       grind)
    | exact superpose eq101930 eq102175
    | exact resolve eq102175 eq101930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101930 eq102175
  have eq102218 : x ≠ y ∨ x = (M.op y x) := by grind
  have eq102542 : x ≠ (M.op x y) ∨ x = (k y x) := by grind
  have eq102970 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq102181 eq102140
    | exact resolve eq102140 eq102181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102140
  have eq102971 : x = (M.op y x) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq102970 x
       have i₂ := eq102181
       grind)
    | exact superpose eq102181 eq102970
    | exact resolve eq102970 eq102181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102181 eq102970
  have eq103029 : x = (M.op y x) ∨ x = y := by grind
  clear eq102971
  have eq103045 : x = (M.op y x) := by
    first
    | (have r₁ := eq103029
       have r₂ := eq102218
       grind)
    | exact resolve eq103029 eq102218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102218 eq103029
  have eq103069 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq103045
       grind)
    | exact superpose eq103045 eq9
    | exact resolve eq9 eq103045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103076 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq211 y x
       have i₂ := eq103045
       grind)
    | exact superpose eq103045 eq211
    | exact resolve eq211 eq103045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103100 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41395 y x
       have i₂ := eq103045
       grind)
    | exact superpose eq103045 eq41395
    | exact resolve eq41395 eq103045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41395
  have eq103101 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq57285 y x
       have i₂ := eq103045
       grind)
    | exact superpose eq103045 eq57285
    | exact resolve eq57285 eq103045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57285 eq103045
  have eq103282 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq21579 (σ y) (σ x)
       have i₂ := eq103101
       grind)
    | exact superpose eq103101 eq21579
    | exact resolve eq21579 eq103101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21579 eq103101
  have eq103303 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq103282
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq103282
    | exact resolve eq103282 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103282
  have eq103321 : (σ x) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq103303
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq103303
    | exact resolve eq103303 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103303
  have eq103327 : (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (k y x) := by
    first
    | exact superpose eq101924 eq103321
    | exact resolve eq103321 eq101924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103321
  have eq103331 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | exact superpose eq101924 eq103327
    | exact resolve eq103327 eq101924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101924 eq103327
  have eq103332 : (σ (M.op x y)) = (σ x) ∨ x = (k y x) := by
    first
    | (have r₁ := eq103331
       have r₂ := eq16
       grind)
    | exact resolve eq103331 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103331
  have eq103336 : (M.op x y) = (τ (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq103332
       grind)
    | exact superpose eq103332 eq10
    | exact resolve eq10 eq103332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103332
  have eq103528 : x = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq103336
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq103336
    | exact resolve eq103336 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103336
  have eq103531 : x = (k y x) := by
    first
    | (have r₁ := eq103528
       have r₂ := eq102542
       grind)
    | exact resolve eq103528 eq102542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102542 eq103528
  have eq103532 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq103076
       have i₂ := eq103531
       grind)
    | exact superpose eq103531 eq103076
    | exact resolve eq103076 eq103531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103076
  have eq110531 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq103100
       have i₂ := eq103531
       grind)
    | exact superpose eq103531 eq103100
    | exact resolve eq103100 eq103531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103100
  have eq110533 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq110531
       grind)
    | exact superpose eq110531 eq16
    | exact resolve eq16 eq110531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110531
  have eq110635 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq110533
       have i₂ := eq103532
       grind)
    | exact superpose eq103532 eq110533
    | exact resolve eq110533 eq103532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103532 eq110533
  have eq110636 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq110635
  have eq110685 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6596 (σ x) (σ y)
       have i₂ := eq110636
       grind)
    | exact superpose eq110636 eq6596
    | exact resolve eq6596 eq110636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6596 eq110636
  have eq110704 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) := by grind
  clear eq110685
  have eq110721 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq110704
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq110704
    | exact resolve eq110704 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110704
  have eq110767 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq62 x y
       have i₂ := eq110721
       grind)
    | exact superpose eq110721 eq62
    | exact resolve eq62 eq110721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110721
  have eq110804 : x = (M.op x x) := by grind
  clear eq110767
  have eq110818 : ∀ X0 : G, x = (M.op (M.op (M.op x x) X0) x) := by
    intro X0
    first
    | (have i₁ := eq9 x x X0
       have i₂ := eq110804
       grind)
    | exact superpose eq110804 eq9
    | exact resolve eq9 eq110804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110879 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq110818 X0
       have i₂ := eq110804
       grind)
    | exact superpose eq110804 eq110818
    | exact resolve eq110818 eq110804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110804 eq110818
  have eq110954 : y = (M.op x y) := by
    first
    | (have i₁ := eq103069 x
       have i₂ := eq110879 y
       grind)
    | exact superpose eq110879 eq103069
    | exact resolve eq103069 eq110879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103069 eq110879
  have eq111134 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq110954
       grind)
    | exact superpose eq110954 eq16
    | exact resolve eq16 eq110954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110954
  have eq111263 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq111134
       have i₂ := eq102180
       grind)
    | exact superpose eq102180 eq111134
    | (have r₁ := eq111134
       have r₂ := eq102180
       grind)
    | exact resolve eq111134 eq102180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102180
  have eq111271 : (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq111263
  have eq111518 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) (σ x) X0
       have i₂ := eq111271
       grind)
    | exact superpose eq111271 eq9
    | exact resolve eq9 eq111271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111525 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq211 (σ y) (σ x)
       have i₂ := eq111271
       grind)
    | exact superpose eq111271 eq211
    | exact resolve eq211 eq111271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq111271
  have eq111567 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq111525
       have r₂ := eq111134
       grind)
    | exact resolve eq111525 eq111134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111525
  have eq111582 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq111567
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq111567
    | exact resolve eq111567 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111567
  have eq111589 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq111582
       have i₂ := eq103531
       grind)
    | exact superpose eq103531 eq111582
    | exact resolve eq111582 eq103531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103531 eq111582
  have eq111595 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq111134
       have i₂ := eq111589
       grind)
    | exact superpose eq111589 eq111134
    | exact resolve eq111134 eq111589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111134
  have eq111622 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq62 (σ x) (σ y)
       have i₂ := eq111589
       grind)
    | exact superpose eq111589 eq62
    | exact resolve eq62 eq111589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq116042 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq111518 X0
       have i₂ := eq111589
       grind)
    | exact superpose eq111589 eq111518
    | exact resolve eq111518 eq111589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111518
  have eq116044 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq116042 (σ x)
       have i₂ := eq111622
       grind)
    | exact superpose eq111622 eq116042
    | exact resolve eq116042 eq111622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111622 eq116042
  have eq116126 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq116044
       have i₂ := eq111589
       grind)
    | exact superpose eq111589 eq116044
    | exact resolve eq116044 eq111589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111589 eq116044
  have eq116140 : False := by grind
  exact eq116140
