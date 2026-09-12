import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pyx_pxx_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq11 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       have r₂ := eq13 X0 (M.op X1 X1)
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y
       grind)
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq45
    | exact resolve eq45 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq134 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq51
    | (have j0 := eq51 (M.op x y)
       grind)
    | exact resolve eq51 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq175 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0 X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 (σ x)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X5 (M.op X0 X1)))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq16 (M.op X0 X1) (M.op x (M.op x X0)) X4 X5
       have i₂ := eq16 X0 X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, y = (M.op (M.op y X0) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 y X0 X1 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y X0 X1 x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) X0 X1 (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X1 X0) X2 (M.op X0 x) x
       have i₂ := eq16 X0 x x X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X2 X3 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X2 (M.op X3 (M.op (σ x) (σ y))))) := by
    intro X2 X3
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq601 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X3 (k X0 X1))) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X2 X3 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq602 : ∀ X0 X1 X2 X3 : G, (M.op (k X0 X1) (M.op X2 (M.op X3 X1))) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 X0 X2 X3
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X1 (k (σ x) X0))) ∨ (M.op X0 X0) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 X1
       have i₂ := eq28 sF2 X1
       grind)
    | exact superpose eq28 eq176
    | (have j1 := eq28 (σ x) X0
       grind)
    | exact resolve eq176 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq621 : (M.op x y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq626 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq631 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq634 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq621
       grind)
    | exact superpose eq621 eq40
    | exact resolve eq40 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq635 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq634
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq634
    | exact resolve eq634 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq637 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq635
    | exact resolve eq635 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq647 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq637 eq626
    | exact resolve eq626 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq654 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq647
       have r₂ := eq27
       grind)
    | exact resolve eq647 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq658 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq654
       have i₂ := eq28 sF2 sF2
       grind)
    | exact superpose eq28 eq654
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq654 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq659 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq654 eq176
    | exact resolve eq176 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq668 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq659
    | (have j0 := eq659 (σ x)
       grind)
    | exact resolve eq659 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq682 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq668 eq181
    | exact resolve eq181 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq668
  have eq692 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq692
    | (have j0 := eq692 X0
       have j1 := eq28 (k (k X0 X0) X0) (k X0 X0)
       grind)
    | exact resolve eq692 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq722 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq654 eq682
    | exact resolve eq682 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq731 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by grind
  clear eq722
  have eq736 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq731 eq179
    | exact resolve eq179 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq889 : (τ (σ y)) = (k x x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq658 eq98
    | exact resolve eq98 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq897 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (k x x) := by
    first
    | exact superpose eq32 eq889
    | exact resolve eq889 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889
  have eq909 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x x) ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq897 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq897
       grind)
    | exact resolve eq13 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq913 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x x) ∨ y = (k x x) := by
    intro X0
    first
    | (have j0 := eq909 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq1076 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq178 eq177
    | exact resolve eq177 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1078 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq179 eq177
    | exact resolve eq177 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1161 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X3 X0)) = (M.op X1 (k X0 X2)) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq177 X1 (k X0 X2) X3 (M.op X0 x)
       have i₂ := eq601 X0 X2 x X1
       grind)
    | exact superpose eq601 eq177
    | (have j1 := eq601 X0 X2 X2 X3
       grind)
    | exact resolve eq177 eq601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1488 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (k x x) := by
    first
    | exact superpose eq913 eq26
    | (have j1 := eq913 (σ y)
       grind)
    | exact resolve eq26 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq1593 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (k x x) := by
    first
    | exact superpose eq637 eq1488
    | exact resolve eq1488 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637 eq1488
  have eq1631 : y = (k x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq1593
       have r₂ := eq27
       grind)
    | exact resolve eq1593 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1593
  have eq1653 : x ≠ y ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq631 x
       have i₂ := eq1631
       grind)
    | exact superpose eq1631 eq631
    | (have j0 := eq631 x
       grind)
    | exact resolve eq631 eq1631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1654 : ∀ X0 X1 : G, x = (M.op (M.op x X0) (M.op X1 y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq601 x x X0 X1
       have i₂ := eq1631
       grind)
    | exact superpose eq1631 eq601
    | (have j0 := eq601 x x x x
       grind)
    | exact resolve eq601 eq1631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1655 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1654 X0 x
       have i₂ := eq1076 (M.op x X0) x
       grind)
    | (have i₁ := eq1654 X0 x
       have i₂ := eq1076 (M.op x X0) x
       grind)
    | exact superpose eq1076 eq1654
    | (have j0 := eq1654 X0 x
       grind)
    | exact resolve eq1654 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1654
  have eq1658 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x y)) ∨ x = (M.op x x) ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq28 eq1655
    | (have j0 := eq1655 X0
       have j1 := eq28 x x
       grind)
    | exact resolve eq1655 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1655
  have eq1661 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x y)) ∨ x = y ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq1631 eq1658
    | (have j0 := eq1658 X0
       grind)
    | exact resolve eq1658 eq1631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1658
  have eq2071 : ∀ X0 X1 : G, x = (M.op y (M.op X0 (M.op X1 x))) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq602 x x X0 X1
       have i₂ := eq1631
       grind)
    | exact superpose eq1631 eq602
    | (have j0 := eq602 x x x x
       grind)
    | exact resolve eq602 eq1631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2209 : ∀ X0 X1 : G, x = (M.op y (M.op X0 (M.op X1 x))) ∨ x = (M.op x x) ∨ y = (k x x) := by
    intro X0 X1
    first
    | exact superpose eq28 eq2071
    | (have j0 := eq2071 X0 X1
       have j1 := eq28 x x
       grind)
    | exact resolve eq2071 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2071
  have eq2222 : ∀ X0 : G, x = (M.op y (M.op X0 (k x x))) ∨ x = (M.op x x) ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq1161 eq2209
    | (have j1 := eq1161 x x x x
       grind)
    | exact resolve eq2209 eq1161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2209
  have eq2227 : ∀ X0 : G, x = (M.op y (M.op X0 (k x x))) ∨ x = y ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq1631 eq2222
    | (have j0 := eq2222 X0
       grind)
    | exact resolve eq2222 eq1631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1631 eq2222
  have eq2520 : ∀ X1 : G, y = (M.op x (M.op X1 (M.op x y))) ∨ x = y ∨ y = (k x x) := by
    intro X1
    first
    | (have i₁ := eq178 (M.op x (k x x)) X1
       have i₂ := eq2227 x
       grind)
    | exact superpose eq2227 eq178
    | exact resolve eq178 eq2227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2227
  have eq2542 : x = (M.op y (M.op x y)) ∨ x = y ∨ y = (k x x) ∨ x = y ∨ y = (k x x) := by
    first
    | exact superpose eq2520 eq1661
    | exact resolve eq1661 eq2520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1661 eq2520
  have eq2557 : y = (k x x) ∨ x = y ∨ x = (M.op y (M.op x y)) := by grind
  clear eq2542
  have eq2568 : ∀ X0 X1 : G, x = (M.op y (M.op X0 (M.op X1 x))) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op y (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq602 x x X0 X1
       have i₂ := eq2557
       grind)
    | exact superpose eq2557 eq602
    | (have j0 := eq602 x x x x
       grind)
    | exact resolve eq602 eq2557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2571 : ∀ X0 : G, x = (M.op y (M.op X0 (k x x))) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1161 eq2568
    | (have j1 := eq1161 x x x x
       grind)
    | exact resolve eq2568 eq1161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2568
  have eq2574 : ∀ X0 : G, x = (M.op y (M.op X0 y)) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2557 eq2571
    | exact resolve eq2571 eq2557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2557 eq2571
  have eq2577 : x = (M.op y (M.op x y)) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq2574 x
       have i₂ := eq1076 y x
       grind)
    | (have i₁ := eq2574 x
       have i₂ := eq1076 y x
       grind)
    | exact superpose eq1076 eq2574
    | (have j0 := eq2574 x
       grind)
    | exact resolve eq2574 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2574
  have eq2578 : x = (M.op y (M.op x y)) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq2577
  have eq2625 : ∀ X0 : G, y = (M.op x (M.op X0 (M.op x y))) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2578 eq178
    | exact resolve eq178 eq2578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq2645 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq2578 eq2625
    | exact resolve eq2625 eq2578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2578 eq2625
  have eq2664 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq2645
  have eq2672 : y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq2664
       have r₂ := eq1653
       grind)
    | exact resolve eq2664 eq1653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1653 eq2664
  have eq2677 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq175 X0 x
       have i₂ := eq2672
       grind)
    | exact superpose eq2672 eq175
    | exact resolve eq175 eq2672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq2682 : y = (k x x) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq2672
       grind)
    | exact superpose eq2672 eq28
    | (have j0 := eq28 x x
       grind)
    | exact resolve eq28 eq2672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2683 : ∀ X0 X1 : G, y = (M.op x (M.op X0 (M.op X1 y))) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq177 x x x x
       have i₂ := eq2672
       grind)
    | exact superpose eq2672 eq177
    | exact resolve eq177 eq2672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2689 : x ≠ y ∨ x = (M.op x x) := by grind
  have eq2692 : ∀ X0 : G, y = (M.op x (M.op X0 (M.op x y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq2683 X0 x
       have i₂ := eq1076 X0 x
       grind)
    | (have i₁ := eq2683 X0 x
       have i₂ := eq1076 X0 x
       grind)
    | exact superpose eq1076 eq2683
    | (have j0 := eq2683 X0 x
       grind)
    | exact resolve eq2683 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2683
  have eq2693 : y = (k x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq2682
       have r₂ := eq2689
       grind)
    | exact resolve eq2682 eq2689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2682
  have eq2697 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2677 x
       have i₂ := eq1076 sF0 x
       grind)
    | (have i₁ := eq2677 x
       have i₂ := eq1076 sF0 x
       grind)
    | exact superpose eq1076 eq2677
    | (have j0 := eq2677 x
       grind)
    | exact resolve eq2677 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076 eq2677
  have eq2702 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq2693
       grind)
    | exact superpose eq2693 eq40
    | exact resolve eq40 eq2693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2693
  have eq2714 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2702
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2702
    | exact resolve eq2702 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2702
  have eq2717 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2714
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2714
    | exact resolve eq2714 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2714
  have eq2720 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq2697
       have i₂ := eq28 sF0 sF0
       grind)
    | exact superpose eq28 eq2697
    | (have j1 := eq28 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq2697 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2730 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2697 eq28
    | (have j0 := eq28 x x
       grind)
    | exact resolve eq28 eq2697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2773 : ∀ X0 X1 : G, (σ x) = (M.op (σ y) (M.op X0 (M.op X1 (σ x)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq2717 eq602
    | (have j0 := eq602 (σ x) (σ x) x x
       grind)
    | exact resolve eq602 eq2717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2774 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op X1 (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq2717 eq601
    | (have j0 := eq601 (σ x) (σ x) x x
       grind)
    | exact resolve eq601 eq2717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2775 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1078 eq2774
    | (have j0 := eq2774 X0 (σ x)
       grind)
    | exact resolve eq2774 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2774
  have eq2776 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op X0 (k (σ x) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1161 eq2773
    | (have j1 := eq1161 (σ x) x (σ x) x
       grind)
    | exact resolve eq2773 eq1161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2773
  have eq2780 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op X0 (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq2717 eq2776
    | exact resolve eq2776 eq2717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2717 eq2776
  have eq2783 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1078 eq2780
    | (have j0 := eq2780 (σ x)
       grind)
    | exact resolve eq2780 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2780
  have eq3666 : y = (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2720 eq2692
    | exact resolve eq2692 eq2720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2720
  have eq3683 : y = (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq3666
  have eq3694 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2730 eq3683
    | exact resolve eq3683 eq2730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2730 eq3683
  have eq3703 : x = y ∨ x = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2697 eq3694
    | exact resolve eq3694 eq2697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3694
  have eq3705 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq3703
       have r₂ := eq2689
       grind)
    | exact resolve eq3703 eq2689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3703
  have eq3708 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3705 eq42
    | exact resolve eq42 eq3705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3709 : (k x (M.op x y)) = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3705 eq693
    | (have j0 := eq693 (M.op x y)
       grind)
    | exact resolve eq693 eq3705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3712 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3705 eq631
    | (have j0 := eq631 (M.op x y)
       grind)
    | exact resolve eq631 eq3705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3705
  have eq3715 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (k x (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2672 eq3709
    | exact resolve eq3709 eq2672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2672 eq3709
  have eq3716 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq3708
    | exact resolve eq3708 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3708
  have eq3718 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3716
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3716
    | exact resolve eq3716 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3716
  have eq3723 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3718 eq693
    | (have j0 := eq693 (σ (M.op x y))
       grind)
    | exact resolve eq693 eq3718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq3726 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3718 eq631
    | (have j0 := eq631 (σ (M.op x y))
       grind)
    | exact resolve eq631 eq3718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3727 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op X1 (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq3718 eq602
    | (have j0 := eq602 (σ (M.op x y)) (σ (M.op x y)) x x
       grind)
    | exact resolve eq602 eq3718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq3729 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (k (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1161 eq3727
    | (have j1 := eq1161 (σ (M.op x y)) x (σ (M.op x y)) x
       grind)
    | exact resolve eq3727 eq1161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161 eq3727
  have eq3733 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq3718 eq3729
    | exact resolve eq3729 eq3718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3729
  have eq3847 : x = (M.op x y) ∨ x = (M.op x x) ∨ y = (k x (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3715 eq2697
    | exact resolve eq2697 eq3715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3854 : y = (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ y = (k x (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3715 eq2692
    | exact resolve eq2692 eq3715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2692 eq3715
  have eq3871 : y = (k x (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op x (M.op x y)) := by grind
  clear eq3854
  have eq3874 : y = (k x (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq3847
  have eq3888 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3874 eq42
    | exact resolve eq42 eq3874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3874
  have eq3891 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3888
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3888
    | exact resolve eq3888 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3888
  have eq3893 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3891
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3891
    | exact resolve eq3891 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3891
  have eq3956 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x x) ∨ y = (M.op x (M.op x y)) := by
    first
    | exact superpose eq3871 eq42
    | exact resolve eq42 eq3871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq3871
  have eq3959 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x x) ∨ y = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq3956
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3956
    | exact resolve eq3956 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3956
  have eq3961 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x x) ∨ y = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq3959
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3959
    | exact resolve eq3959 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3959
  have eq3963 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x x) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3893 eq3961
    | exact resolve eq3961 eq3893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3893 eq3961
  have eq3965 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq2697 eq3963
    | exact resolve eq3963 eq2697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2697 eq3963
  have eq3967 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq3965
       have r₂ := eq2689
       grind)
    | exact resolve eq3965 eq2689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3965
  have eq3974 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op X1 (σ y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq3967 eq601
    | (have j0 := eq601 (σ x) (σ (M.op x y)) x x
       grind)
    | exact resolve eq601 eq3967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq3975 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1078 eq3974
    | (have j0 := eq3974 X0 (σ x)
       grind)
    | exact resolve eq3974 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3974
  have eq3979 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq682 eq3975
    | (have j0 := eq3975 X0
       have j1 := eq682 X0
       grind)
    | exact resolve eq3975 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682 eq3975
  have eq4207 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq3979 eq179
    | exact resolve eq179 eq3979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq3979
  have eq4294 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2783 eq4207
    | exact resolve eq4207 eq2783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2783 eq4207
  have eq4332 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq4294
       have r₂ := eq2689
       grind)
    | exact resolve eq4294 eq2689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4294
  have eq4334 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq654 eq4332
    | exact resolve eq4332 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4332
  have eq4335 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq28 eq4334
    | (have j1 := eq28 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq4334 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4334
  have eq6833 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq2775
    | (have j0 := eq2775 (σ y)
       grind)
    | exact resolve eq2775 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2775
  have eq9345 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (k (σ x) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq3723 eq176
    | exact resolve eq176 eq3723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq9363 : ∀ X0 X1 : G, (k (σ x) (σ (M.op x y))) = (M.op (σ x) (M.op X0 (M.op X1 (k (σ x) (σ (M.op x y)))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq3723 eq177
    | exact resolve eq177 eq3723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq3723
  have eq9392 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (M.op X0 (M.op X1 (σ y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq3967 eq9363
    | exact resolve eq9363 eq3967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9363
  have eq9400 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (k (σ x) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq611 eq9345
    | (have j0 := eq9345 X0
       have j1 := eq611 (σ (M.op x y)) X0
       grind)
    | exact resolve eq9345 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611 eq9345
  have eq9416 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1078 eq9392
    | (have j0 := eq9392 X0 (σ x)
       grind)
    | exact resolve eq9392 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9392
  have eq9421 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq3967 eq9400
    | exact resolve eq9400 eq3967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3967 eq9400
  have eq9430 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq736 eq9416
    | (have j0 := eq9416 X0
       have j1 := eq736 X0
       grind)
    | exact resolve eq9416 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736 eq9416
  have eq9434 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1078 eq9421
    | (have j0 := eq9421 (σ x)
       grind)
    | exact resolve eq9421 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078 eq9421
  have eq9443 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq9434 eq188
    | exact resolve eq188 eq9434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq9558 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq9434 eq9430
    | exact resolve eq9430 eq9434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9434
  have eq9559 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq6833 eq9430
    | exact resolve eq9430 eq6833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6833 eq9430
  have eq9606 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq9559
       have r₂ := eq2689
       grind)
    | exact resolve eq9559 eq2689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9559
  have eq9607 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq9558
       have r₂ := eq3726
       grind)
    | exact resolve eq9558 eq3726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9558
  have eq9610 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq654 eq9606
    | exact resolve eq9606 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9606
  have eq9611 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq9607
       have r₂ := eq2689
       grind)
    | exact resolve eq9607 eq2689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2689 eq9607
  have eq9614 : (σ y) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq28 eq9610
    | (have j1 := eq28 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq9610 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9610
  have eq9615 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq654 eq9611
    | exact resolve eq9611 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654 eq9611
  have eq9618 : (σ y) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq4335 eq9614
    | exact resolve eq9614 eq4335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4335 eq9614
  have eq9624 : (σ y) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq9615
       have i₂ := eq28 sF2 sF2
       grind)
    | exact superpose eq28 eq9615
    | (have j1 := eq28 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq9615 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9615
  have eq9678 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq9618 eq9624
    | exact resolve eq9624 eq9618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9618 eq9624
  have eq9679 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq9678
  have eq9796 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq9679 eq98
    | exact resolve eq98 eq9679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq9679
  have eq9822 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq32 eq9796
    | exact resolve eq9796 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq9796
  have eq10022 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (k x x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq9822 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq9822
       grind)
    | exact resolve eq13 eq9822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9822
  have eq10038 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (k x x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq10022 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10022
  have eq11758 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq10038 eq26
    | (have j1 := eq10038 (σ y)
       grind)
    | exact resolve eq26 eq10038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10038
  have eq14732 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3733 eq9443
    | exact resolve eq9443 eq3733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3733 eq9443
  have eq14781 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq14732
  have eq14806 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq14781
       have r₂ := eq3726
       grind)
    | exact resolve eq14781 eq3726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3726 eq14781
  have eq14843 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq14806
       have r₂ := eq27
       grind)
    | exact resolve eq14806 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14806
  have eq14866 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq14843 eq13
    | (have j0 := eq13 X0 (σ (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (σ (M.op x y))
       have r₂ := eq14843
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq14843
       grind)
    | exact resolve eq13 eq14843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14883 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq14866 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14866
  have eq14990 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq14883 eq14843
    | exact resolve eq14843 eq14883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14843 eq14883
  have eq15160 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by grind
  clear eq14990
  have eq15204 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3718 eq15160
    | exact resolve eq15160 eq3718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3718 eq15160
  have eq15259 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq15204
       grind)
    | exact superpose eq15204 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq15204
       grind)
    | exact resolve eq13 eq15204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15276 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq15259 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15259
  have eq15662 : x = (k x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq15204
       have i₂ := eq15276 x
       grind)
    | exact superpose eq15276 eq15204
    | exact resolve eq15204 eq15276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15204
  have eq15664 : (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq15276 y
       grind)
    | exact superpose eq15276 eq18
    | (have j1 := eq15276 y
       grind)
    | exact resolve eq18 eq15276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15276
  have eq15812 : x = (k x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq15662
  have eq15945 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq15664
       grind)
    | exact superpose eq15664 eq40
    | exact resolve eq40 eq15664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15664
  have eq15948 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq15945
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15945
    | exact resolve eq15945 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15945
  have eq15952 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq15948
    | exact resolve eq15948 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15948
  have eq15983 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq15812
       grind)
    | exact superpose eq15812 eq40
    | exact resolve eq40 eq15812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq15812
  have eq16003 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq15983
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15983
    | exact resolve eq15983 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq15983
  have eq16183 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq15952 eq626
    | exact resolve eq626 eq15952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq16205 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq16183
       have r₂ := eq27
       grind)
    | exact resolve eq16183 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16183
  have eq16330 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq16205 eq28
    | exact resolve eq28 eq16205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq16205
  have eq16360 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq16003 eq16330
    | exact resolve eq16330 eq16003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16330
  have eq16361 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq16360
  have eq16433 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq16361 eq15952
    | exact resolve eq15952 eq16361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15952 eq16361
  have eq16434 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq16433
  have eq16446 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq16003 eq16434
    | exact resolve eq16434 eq16003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16003 eq16434
  have eq16447 : (σ (M.op x y)) = (σ x) := by grind
  clear eq16446
  have eq16476 : (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq16447 eq29
    | exact resolve eq29 eq16447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq16484 : (k (M.op x y) (M.op x y)) = (τ (k (σ x) (σ x))) := by
    first
    | exact superpose eq16447 eq134
    | exact resolve eq134 eq16447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq16509 : (k (M.op x y) (M.op x y)) = (k x (τ (σ x))) := by
    first
    | exact superpose eq91 eq16484
    | exact resolve eq16484 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq16484
  have eq16516 : (k x x) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq30 eq16509
    | exact resolve eq16509 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16509
  have eq16526 : x = (M.op x y) := by
    first
    | exact superpose eq16476 eq30
    | exact resolve eq30 eq16476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq16531 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq16476 eq14
    | exact resolve eq14 eq16476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16476
  have eq16532 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq16526
       grind)
    | exact superpose eq16526 eq18
    | exact resolve eq18 eq16526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq16580 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq3712
       have i₂ := eq16526
       grind)
    | exact superpose eq16526 eq3712
    | (have r₁ := eq3712
       have r₂ := eq16526
       grind)
    | exact resolve eq3712 eq16526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3712
  have eq16611 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq16580
  have eq16612 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq16611
  have eq16752 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq16612 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq16612
       grind)
    | exact resolve eq13 eq16612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16769 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have j0 := eq16752 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16752
  have eq17725 : (M.op x y) = (k y (M.op x y)) := by
    first
    | exact superpose eq16769 eq16532
    | exact resolve eq16532 eq16769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16532
  have eq17728 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq16769 eq16612
    | exact resolve eq16612 eq16769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16612 eq16769
  have eq18188 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq17725 eq37
    | exact resolve eq37 eq17725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq17725
  have eq18197 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq18188
    | exact resolve eq18188 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18188
  have eq18200 : (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq16447 eq18197
    | exact resolve eq18197 eq16447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18197
  have eq18316 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq17728 eq38
    | exact resolve eq38 eq17728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq18331 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq18316
    | exact resolve eq18316 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq18316
  have eq18333 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq16447 eq18331
    | exact resolve eq18331 eq16447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18331
  have eq18350 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq18200 eq11758
    | exact resolve eq11758 eq18200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11758 eq18200
  have eq18367 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq18350
       have i₂ := eq16516
       grind)
    | exact superpose eq16516 eq18350
    | exact resolve eq18350 eq16516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16516 eq18350
  have eq18375 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq17728 eq18367
    | exact resolve eq18367 eq17728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17728 eq18367
  have eq18380 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18375
       have i₂ := eq16526
       grind)
    | exact superpose eq16526 eq18375
    | exact resolve eq18375 eq16526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16526 eq18375
  have eq18381 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq18380
  have eq18423 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18333 eq631
    | (have j0 := eq631 (σ x)
       grind)
    | (have r₁ := eq631 (σ x)
       have r₂ := eq18333
       grind)
    | exact resolve eq631 eq18333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631 eq18333
  have eq18426 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq18423
  have eq18742 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18381 eq27
    | exact resolve eq27 eq18381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18381
  have eq18832 : y = (M.op x y) := by
    first
    | (have r₁ := eq18742
       have r₂ := eq16447
       grind)
    | exact resolve eq18742 eq16447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18742
  have eq18852 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq18832
       grind)
    | exact superpose eq18832 eq24
    | exact resolve eq24 eq18832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq18832
  have eq18936 : (σ x) = (σ y) := by
    first
    | exact superpose eq16531 eq18852
    | exact resolve eq18852 eq16531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16531 eq18852
  have eq18966 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18936 eq26
    | exact resolve eq26 eq18936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq18936
  have eq19067 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18426 eq18966
    | exact resolve eq18966 eq18426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18426 eq18966
  have eq19105 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq19067 eq27
    | exact resolve eq27 eq19067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq19067
  have eq19195 : False := by grind
  exact eq19195

/-- `Equation1480`: `x = (y ◇ x) ◇ (x ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pyx_pxx_pyx_Equation1480 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1480 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1480.models_iff G M).mp hM
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
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X0) = X0 := by
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
  clear eq18
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq79 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq84 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq56 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq56
    | exact resolve eq56 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq197 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq186 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq186
    | (have j0 := eq186 X0
       grind)
    | exact resolve eq186 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq186
  have eq200 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq197 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq197
    | (have j0 := eq197 X0
       grind)
    | exact resolve eq197 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq201 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq200 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq200 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq200 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq208 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq201 (σ X0)
       grind)
    | exact superpose eq201 eq15
    | exact resolve eq15 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq208 X0
       have i₂ := eq201 X0
       grind)
    | exact superpose eq201 eq208
    | exact resolve eq208 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201 eq208
  have eq316 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq16
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq1036 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq84 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq84
    | exact resolve eq84 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq1087 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1036 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1036
    | (have j0 := eq1036 X0 X1
       grind)
    | exact resolve eq1036 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq1200 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq323 (τ X1) (τ X0)
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq323
    | (have j0 := eq323 (τ X0) (τ X1)
       grind)
    | exact resolve eq323 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1208 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1200 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1200
    | (have j0 := eq1200 X0 X1
       grind)
    | exact resolve eq1200 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200
  have eq1211 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1208 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1208
    | (have j0 := eq1208 X0 X1
       grind)
    | exact resolve eq1208 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq1213 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1211 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1211
    | (have j0 := eq1211 X0 X1
       grind)
    | exact resolve eq1211 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211
  have eq1214 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
  have eq1215 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ X0 = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1214 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1214
    | (have j0 := eq1214 X0 X1
       grind)
    | exact resolve eq1214 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1216 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1215 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1215
    | (have j0 := eq1215 X0 X1
       grind)
    | exact resolve eq1215 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215
  have eq1349 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq316
       have i₂ := eq1087 x y
       grind)
    | exact superpose eq1087 eq316
    | (have j1 := eq1087 (σ x) (σ y)
       grind)
    | (have r₁ := eq316
       have r₂ := eq1087 x y
       grind)
    | (have r₁ := eq316
       have r₂ := eq1087 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq316
       have r₂ := eq1087 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq316 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316 eq1087
  have eq1350 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq1349
  have eq9436 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1350
       grind)
    | exact superpose eq1350 eq16
    | exact resolve eq16 eq1350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1350
  have eq9437 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq9436
       have r₂ := eq219 x
       grind)
    | exact resolve eq9436 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9436
  have eq9537 : y ≠ y ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq9437
       grind)
    | exact superpose eq9437 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq9437
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq9437
       grind)
    | exact resolve eq12 eq9437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9437
  have eq9550 : y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9537
  have eq9559 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq323 x y
       have i₂ := eq9550
       grind)
    | exact superpose eq9550 eq323
    | (have j0 := eq323 x y
       grind)
    | exact resolve eq323 eq9550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323 eq9550
  have eq9574 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9559
  have eq9575 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq9574
  have eq9698 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9575
       grind)
    | exact superpose eq9575 eq16
    | exact resolve eq16 eq9575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9707 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq9575
       grind)
    | exact superpose eq9575 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq9575
       grind)
    | exact resolve eq12 eq9575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9575
  have eq9720 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq9707
  have eq9726 : (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq9720
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq9720
    | exact resolve eq9720 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9720
  have eq9847 : y = (τ (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq9726
       grind)
    | exact superpose eq9726 eq10
    | exact resolve eq10 eq9726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9726
  have eq9932 : x = y ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq9847
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9847
    | exact resolve eq9847 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9847
  have eq9950 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9932
       grind)
    | exact superpose eq9932 eq16
    | exact resolve eq16 eq9932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9932
  have eq9951 : (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq9950
       have r₂ := eq219 x
       grind)
    | exact resolve eq9950 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9950
  have eq10024 : (k y x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq9951
       grind)
    | exact superpose eq9951 eq10
    | exact resolve eq10 eq9951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9951
  have eq10111 : y = (k y x) := by
    first
    | (have i₁ := eq10024
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq10024
    | exact resolve eq10024 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10024
  have eq10143 : y ≠ y ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1216 y x
       have i₂ := eq10111
       grind)
    | exact superpose eq10111 eq1216
    | (have j0 := eq1216 x y
       grind)
    | (have r₁ := eq1216 y x
       have r₂ := eq10111
       grind)
    | exact resolve eq1216 eq10111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216 eq10111
  have eq10151 : x = y ∨ y = (M.op x y) := by grind
  clear eq10143
  have eq10304 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10151
       grind)
    | exact superpose eq10151 eq16
    | exact resolve eq16 eq10151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10151
  have eq10309 : y = (M.op x y) := by
    first
    | (have r₁ := eq10304
       have r₂ := eq219 x
       grind)
    | exact resolve eq10304 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10304
  have eq10313 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9698
       have i₂ := eq10309
       grind)
    | exact superpose eq10309 eq9698
    | exact resolve eq9698 eq10309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9698 eq10309
  have eq10330 : (σ x) = (σ y) := by grind
  clear eq10313
  have eq10494 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq10330
       grind)
    | exact superpose eq10330 eq10
    | exact resolve eq10 eq10330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10330
  have eq10584 : x = y := by
    first
    | (have i₁ := eq10494
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10494
    | exact resolve eq10494 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10494
  have eq10606 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10584
       grind)
    | exact superpose eq10584 eq16
    | exact resolve eq16 eq10584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10584
  have eq10612 : False := by grind
  exact eq10612

/-- `Equation1480`: `x = (y ◇ x) ◇ (x ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pyx_pyy_pyx_Equation1480 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1480 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1480.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq297 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq297 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq297 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq297 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq309 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq298 (σ X0)
       grind)
    | exact superpose eq298 eq15
    | exact resolve eq15 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq315 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq298 (τ X0)
       grind)
    | exact superpose eq298 eq31
    | exact resolve eq31 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq322 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq315 X0
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq315
    | exact resolve eq315 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq328 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq309 X0
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq309
    | exact resolve eq309 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298 eq309
  have eq567 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq584 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq567 X0 X1
       have i₂ := eq328 X0
       grind)
    | exact superpose eq328 eq567
    | (have j0 := eq567 X0 X1
       grind)
    | exact resolve eq567 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq3265 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq584 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq584
    | exact resolve eq584 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq3358 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3265 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq3265
    | (have j0 := eq3265 X0 X1
       grind)
    | exact resolve eq3265 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3265
  have eq3363 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3358 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq3358 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq3358 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3358
  have eq3364 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3363 X0 X1
       have i₂ := eq322 X0
       grind)
    | exact superpose eq322 eq3363
    | (have j0 := eq3363 X0 X1
       grind)
    | exact resolve eq3363 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322 eq3363
  have eq3365 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3364 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3364
    | (have j0 := eq3364 X0 X1
       grind)
    | exact resolve eq3364 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3364
  have eq3366 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3365 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3365
    | exact resolve eq3365 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3386 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq3365 (σ X0) X1
       grind)
    | exact superpose eq3365 eq15
    | (have j1 := eq3365 (σ X0) X1
       grind)
    | exact resolve eq15 eq3365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3365
  have eq3447 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3386 X0 X1
       have i₂ := eq328 X0
       grind)
    | exact superpose eq328 eq3386
    | (have j0 := eq3386 X0 X1
       grind)
    | exact resolve eq3386 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3386
  have eq3504 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq3366 (τ X1) X0
       grind)
    | exact superpose eq3366 eq17
    | (have j1 := eq3366 (τ X1) X0
       grind)
    | exact resolve eq17 eq3366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq3366
  have eq3940 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3504 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3504
    | exact resolve eq3504 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3504
  have eq3992 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3940 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3940
    | (have j0 := eq3940 X0 X1
       grind)
    | exact resolve eq3940 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3940
  have eq4471 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3447 x y
       grind)
    | exact superpose eq3447 eq16
    | (have j1 := eq3447 x y
       grind)
    | exact resolve eq16 eq3447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4503 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3447 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3447
  have eq4535 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq4471
       have i₂ := eq3992 y x
       grind)
    | exact superpose eq3992 eq4471
    | (have j1 := eq3992 y x
       grind)
    | (have r₁ := eq4471
       have r₂ := eq3992 y x
       grind)
    | exact resolve eq4471 eq3992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4471
  have eq4536 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq4535
  have eq4541 : x ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq4536
       grind)
    | exact superpose eq4536 eq12
    | (have j0 := eq12 x x
       grind)
    | exact resolve eq12 eq4536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4542 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq4536
       grind)
    | exact superpose eq4536 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq4536
       grind)
    | exact resolve eq13 eq4536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4536
  have eq4548 : x = (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq4542
  have eq4549 : (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq4541
       have r₂ := eq4548
       grind)
    | exact resolve eq4541 eq4548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4541 eq4548
  have eq4582 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4503 x y
       have i₂ := eq4549
       grind)
    | exact superpose eq4549 eq4503
    | (have j0 := eq4503 x y
       grind)
    | exact resolve eq4503 eq4549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4503 eq4549
  have eq4605 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq4582
  have eq4606 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq4605
  have eq4754 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4606
       grind)
    | exact superpose eq4606 eq16
    | exact resolve eq16 eq4606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4760 : (σ x) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq4606
       grind)
    | exact superpose eq4606 eq12
    | exact resolve eq12 eq4606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4761 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq4606
       grind)
    | exact superpose eq4606 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq4606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4606
  have eq4767 : (σ x) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq4761
       have r₂ := eq328 x
       grind)
    | exact resolve eq4761 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4761
  have eq4768 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4760
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4760
    | exact resolve eq4760 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4760
  have eq4769 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4767
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4767
    | exact resolve eq4767 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4767
  have eq4770 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4769
       have i₂ := eq328 x
       grind)
    | exact superpose eq328 eq4769
    | exact resolve eq4769 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328 eq4769
  have eq4771 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq4770
       have r₂ := eq4768
       grind)
    | exact resolve eq4770 eq4768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4768 eq4770
  have eq4779 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3992 y x
       have i₂ := eq4771
       grind)
    | exact superpose eq4771 eq3992
    | (have j0 := eq3992 y x
       grind)
    | exact resolve eq3992 eq4771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3992 eq4771
  have eq4836 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq4779
       have r₂ := eq4754
       grind)
    | exact resolve eq4779 eq4754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4779
  have eq4853 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4754
       have i₂ := eq4836
       grind)
    | exact superpose eq4836 eq4754
    | exact resolve eq4754 eq4836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4754 eq4836
  have eq4864 : False := by grind
  exact eq4864

/-- `Equation1480`: `x = (y ◇ x) ◇ (x ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyx_pyx_pxx_pyx_Equation1480 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1480 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1480.models_iff G M).mp hM
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
  have eq84 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq186 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq84 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq84 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq84 X0 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq13 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq190 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq186 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq191 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq190 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq193 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq191 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq191
    | (have j0 := eq191 X0 X1
       grind)
    | exact resolve eq191 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq197 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq193 X0 X1
       have j1 := eq189 X1 X0
       grind)
    | (have r₁ := eq193 X1 X0
       have r₂ := eq189 X0 X1
       grind)
    | (have r₁ := eq193 (k X1 X0) X1
       have r₂ := eq189 X0 X1
       grind)
    | (have r₁ := eq193 X1 X1
       have r₂ := eq189 X1 X1
       grind)
    | exact resolve eq193 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq193
  have eq566 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq197 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq197
    | exact resolve eq197 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq580 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq197 y x
       grind)
    | exact superpose eq197 eq16
    | (have j1 := eq197 y x
       grind)
    | exact resolve eq16 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq598 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq566 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq566
    | (have j0 := eq566 X0 X1
       grind)
    | exact resolve eq566 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq566
  have eq599 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq598 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq598
    | exact resolve eq598 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq658 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq599 (τ X1) X0
       grind)
    | exact superpose eq599 eq18
    | (have j1 := eq599 (τ X1) X0
       grind)
    | exact resolve eq18 eq599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq599
  have eq900 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq658 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq658
    | exact resolve eq658 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq951 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq900 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq900
    | (have j0 := eq900 X0 X1
       grind)
    | exact resolve eq900 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq1048 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq580
       have i₂ := eq951 y x
       grind)
    | exact superpose eq951 eq580
    | (have j1 := eq951 (σ y) (σ x)
       grind)
    | (have r₁ := eq580
       have r₂ := eq951 y x
       grind)
    | exact resolve eq580 eq951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1049 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1048
  have eq1053 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1049
  have eq1104 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq580
       have i₂ := eq1053
       grind)
    | exact superpose eq1053 eq580
    | exact resolve eq580 eq1053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580 eq1053
  have eq1105 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1104
  have eq1106 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1105
  have eq1118 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1106
  have eq1130 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1118
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1118
    | exact resolve eq1118 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118
  have eq1177 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1130
       grind)
    | exact superpose eq1130 eq16
    | exact resolve eq16 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130
  have eq1192 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1177
       have i₂ := eq951 y x
       grind)
    | exact superpose eq951 eq1177
    | (have j1 := eq951 y x
       grind)
    | (have r₁ := eq1177
       have r₂ := eq951 y x
       grind)
    | exact resolve eq1177 eq951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq1193 : y = (M.op x x) := by grind
  clear eq1192
  have eq1229 : (M.op x y) = (k y x) := by grind
  clear eq1193
  have eq1240 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1177
       have i₂ := eq1229
       grind)
    | exact superpose eq1229 eq1177
    | exact resolve eq1177 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177 eq1229
  have eq1243 : False := by grind
  exact eq1243

/-- `Equation1480`: `x = (y ◇ x) ◇ (x ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_Equation1480 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1480 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1480.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq84 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq188 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq84 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq84 X1 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq13 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq193 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq188 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq194 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq193 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq196 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq194 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq194
    | (have j0 := eq194 X0 X1
       grind)
    | exact resolve eq194 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq200 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq196 X0 X1
       have j1 := eq192 X0 X1
       grind)
    | (have r₁ := eq196 X0 X1
       have r₂ := eq192 X0 X1
       grind)
    | (have r₁ := eq196 X0 (k X1 X0)
       have r₂ := eq192 X0 X1
       grind)
    | (have r₁ := eq196 X0 X0
       have r₂ := eq192 X0 X0
       grind)
    | exact resolve eq196 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq196
  have eq571 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq200 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq200
    | exact resolve eq200 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq200 x y
       grind)
    | exact superpose eq200 eq16
    | (have j1 := eq200 x y
       grind)
    | exact resolve eq16 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq603 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq571 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq571
    | (have j0 := eq571 X0 X1
       grind)
    | exact resolve eq571 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq571
  have eq604 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq603 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq603
    | exact resolve eq603 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq663 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq604 (τ X1) X0
       grind)
    | exact superpose eq604 eq18
    | (have j1 := eq604 (τ X1) X0
       grind)
    | exact resolve eq18 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq604
  have eq875 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq663 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq663
    | exact resolve eq663 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq922 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq875 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq875
    | (have j0 := eq875 X0 X1
       grind)
    | exact resolve eq875 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875
  have eq1039 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq585
       have i₂ := eq922 y x
       grind)
    | exact superpose eq922 eq585
    | (have j1 := eq922 (σ y) (σ x)
       grind)
    | (have r₁ := eq585
       have r₂ := eq922 y x
       grind)
    | exact resolve eq585 eq922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1040 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1039
  have eq1044 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1040
  have eq1058 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq585
       have i₂ := eq1044
       grind)
    | exact superpose eq1044 eq585
    | exact resolve eq585 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585 eq1044
  have eq1059 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1058
  have eq1060 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1059
  have eq1070 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1060
  have eq1082 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1070
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1070
    | exact resolve eq1070 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070
  have eq1130 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1082
       grind)
    | exact superpose eq1082 eq16
    | exact resolve eq16 eq1082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082
  have eq1144 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1130
       have i₂ := eq922 y x
       grind)
    | exact superpose eq922 eq1130
    | (have j1 := eq922 y x
       grind)
    | (have r₁ := eq1130
       have r₂ := eq922 y x
       grind)
    | exact resolve eq1130 eq922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq1145 : y = (M.op x x) := by grind
  clear eq1144
  have eq1195 : (M.op x y) = (k y x) := by grind
  clear eq1145
  have eq1206 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1130
       have i₂ := eq1195
       grind)
    | exact superpose eq1195 eq1130
    | exact resolve eq1130 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130 eq1195
  have eq1209 : False := by grind
  exact eq1209

/-- `Equation1481`: `x = (y ◇ x) ◇ (x ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pyx_pyy_pyx_Equation1481 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1481 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1481.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq273 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq273 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq273 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq273 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq285 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq274 (σ X0)
       grind)
    | exact superpose eq274 eq15
    | exact resolve eq15 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq291 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq274 (τ X0)
       grind)
    | exact superpose eq274 eq31
    | exact resolve eq31 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq298 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq291 X0
       have i₂ := eq274 X0
       grind)
    | exact superpose eq274 eq291
    | exact resolve eq291 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq304 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq285 X0
       have i₂ := eq274 X0
       grind)
    | exact superpose eq274 eq285
    | exact resolve eq285 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274 eq285
  have eq467 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq484 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq467 X0 X1
       have i₂ := eq304 X0
       grind)
    | exact superpose eq304 eq467
    | (have j0 := eq467 X0 X1
       grind)
    | exact resolve eq467 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq579 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq484 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq484
    | exact resolve eq484 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq613 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq579 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq579
    | (have j0 := eq579 X0 X1
       grind)
    | exact resolve eq579 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq579
  have eq618 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq613 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq613 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq613 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq619 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq618 X0 X1
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq618
    | (have j0 := eq618 X0 X1
       grind)
    | exact resolve eq618 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298 eq618
  have eq620 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq619 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq619
    | (have j0 := eq619 X0 X1
       grind)
    | exact resolve eq619 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq621 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq620 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq620
    | exact resolve eq620 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq627 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq620 (σ X0) X1
       grind)
    | exact superpose eq620 eq15
    | (have j1 := eq620 (σ X0) X1
       grind)
    | exact resolve eq15 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq651 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq627 X0 X1
       have i₂ := eq304 X0
       grind)
    | exact superpose eq304 eq627
    | (have j0 := eq627 X0 X1
       grind)
    | exact resolve eq627 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq680 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq621 (τ X1) X0
       grind)
    | exact superpose eq621 eq17
    | (have j1 := eq621 (τ X1) X0
       grind)
    | exact resolve eq17 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq621
  have eq800 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq680 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq680
    | exact resolve eq680 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq848 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq800 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq800
    | (have j0 := eq800 X0 X1
       grind)
    | exact resolve eq800 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq2615 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq651 x y
       grind)
    | exact superpose eq651 eq16
    | (have j1 := eq651 x y
       grind)
    | exact resolve eq16 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2638 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq651 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq2669 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2615
       have i₂ := eq848 y x
       grind)
    | exact superpose eq848 eq2615
    | (have j1 := eq848 y x
       grind)
    | (have r₁ := eq2615
       have r₂ := eq848 y x
       grind)
    | exact resolve eq2615 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2615
  have eq2670 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2669
  have eq2674 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq2670
       grind)
    | exact superpose eq2670 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2670
       grind)
    | exact resolve eq13 eq2670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2676 : x ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq2670
       grind)
    | exact superpose eq2670 eq12
    | (have j0 := eq12 x x
       grind)
    | exact resolve eq12 eq2670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2670
  have eq2679 : x = (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2674
  have eq2680 : (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq2679
       have r₂ := eq2676
       grind)
    | exact resolve eq2679 eq2676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2676 eq2679
  have eq2705 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2638 x y
       have i₂ := eq2680
       grind)
    | exact superpose eq2680 eq2638
    | (have j0 := eq2638 x y
       grind)
    | exact resolve eq2638 eq2680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2638 eq2680
  have eq2728 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2705
  have eq2729 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2728
  have eq2813 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2729
       grind)
    | exact superpose eq2729 eq16
    | exact resolve eq16 eq2729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2816 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq2729
       grind)
    | exact superpose eq2729 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq2729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2818 : (σ x) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq2729
       grind)
    | exact superpose eq2729 eq12
    | exact resolve eq12 eq2729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2729
  have eq2821 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq2818
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2818
    | exact resolve eq2818 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2818
  have eq2822 : (σ x) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq2816
       have r₂ := eq304 x
       grind)
    | exact resolve eq2816 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2816
  have eq2823 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2822
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2822
    | exact resolve eq2822 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2822
  have eq2824 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2823
       have i₂ := eq304 x
       grind)
    | exact superpose eq304 eq2823
    | exact resolve eq2823 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304 eq2823
  have eq2825 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq2824
       have r₂ := eq2821
       grind)
    | exact resolve eq2824 eq2821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2821 eq2824
  have eq2894 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq848 y x
       have i₂ := eq2825
       grind)
    | exact superpose eq2825 eq848
    | (have j0 := eq848 y x
       grind)
    | exact resolve eq848 eq2825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848 eq2825
  have eq2944 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq2894
       have r₂ := eq2813
       grind)
    | exact resolve eq2894 eq2813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2894
  have eq2961 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq2813
       have i₂ := eq2944
       grind)
    | exact superpose eq2944 eq2813
    | exact resolve eq2813 eq2944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2813 eq2944
  have eq2970 : False := by grind
  exact eq2970

/-- `Equation1481`: `x = (y ◇ x) ◇ (x ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pxy_pyx_Equation1481 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1481 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1481.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq269 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) ≠ (M.op X2 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq13 X2 X0
       grind)
    | exact superpose eq13 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq13 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ (M.op X2 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq269 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq1878 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq270 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1939 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1878 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1878
  have eq1940 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1939 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1939
  have eq2093 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq1940 (τ X0)
       grind)
    | exact superpose eq1940 eq31
    | exact resolve eq31 eq1940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq2140 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2093 X0
       have i₂ := eq1940 X0
       grind)
    | exact superpose eq1940 eq2093
    | exact resolve eq2093 eq1940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1940 eq2093
  have eq2318 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (τ X0)
       have i₂ := eq2140 X0
       grind)
    | exact superpose eq2140 eq14
    | (have j0 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq14 eq2140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2320 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq2140 X0
       grind)
    | exact superpose eq2140 eq12
    | (have j0 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq12 eq2140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2140
  have eq2323 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq2318 X0 X1
       have j1 := eq2320 X0 X1
       grind)
    | (have r₁ := eq2318 X0 X1
       have r₂ := eq2320 X0 X1
       grind)
    | exact resolve eq2318 eq2320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2318 eq2320
  have eq2510 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2323 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2323
    | exact resolve eq2323 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2323
  have eq2540 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq270 X0 X1 X1
       have i₂ := eq2510 X0 X1
       grind)
    | (have i₁ := eq270 X1 X1 X0
       have i₂ := eq2510 X0 X1
       grind)
    | exact superpose eq2510 eq270
    | (have j0 := eq270 X0 X2 X2
       have j1 := eq2510 X0 X2
       grind)
    | (have r₁ := eq270 X1 X1 X0
       have r₂ := eq2510 X0 X1
       grind)
    | (have r₁ := eq270 X0 X1 X1
       have r₂ := eq2510 X0 X1
       grind)
    | exact resolve eq270 eq2510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq2510
  have eq2557 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2540 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2540
  have eq2558 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2557 X0 X2 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2557
  have eq2658 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2558 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2558
  have eq2659 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2658 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2658
  have eq2698 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq2659 (σ X1) (σ X0)
       grind)
    | exact superpose eq2659 eq15
    | exact resolve eq15 eq2659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2813 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2698 X0 X1
       have i₂ := eq2659 X1 X0
       grind)
    | exact superpose eq2659 eq2698
    | exact resolve eq2698 eq2659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2659 eq2698
  have eq3965 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2813 x y
       grind)
    | exact superpose eq2813 eq16
    | (have r₁ := eq16
       have r₂ := eq2813 x y
       grind)
    | exact resolve eq16 eq2813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2813
  have eq3985 : False := by grind
  exact eq3985

/-- `Equation1483`: `x = (y ◇ x) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pxy_y_pxy_Equation1483 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1483 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1483.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq22
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
  have eq78 : y ≠ (M.op x y) ∨ y = (M.op y x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq96 x y
       grind)
    | exact superpose eq96 eq44
    | (have j1 := eq96 x y
       grind)
    | exact resolve eq44 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq108
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq108
    | exact resolve eq108 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq121 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq119
    | exact resolve eq119 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq122 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq121
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq121
    | exact resolve eq121 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq122 eq96
    | (have j0 := eq96 (σ x) (σ y)
       grind)
    | exact resolve eq96 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq125
    | exact resolve eq125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq126
       have r₂ := eq27
       grind)
    | exact resolve eq126 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq131 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq129
    | exact resolve eq129 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq133 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq131 eq27
    | exact resolve eq27 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq716 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq131 eq79
    | (have r₁ := eq79
       have r₂ := eq131
       grind)
    | exact resolve eq79 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq131
  have eq717 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq716
  have eq720 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq717 eq122
    | exact resolve eq122 eq717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq724 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq720
  have eq729 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq724
       have r₂ := eq133
       grind)
    | exact resolve eq724 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq724
  have eq737 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq729 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq729
       grind)
    | exact resolve eq13 eq729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq745 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq737
  have eq751 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq745
    | exact resolve eq745 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq751 eq122
    | exact resolve eq122 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq751
  have eq826 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq823
  have eq830 : y = (M.op x y) := by
    first
    | (have r₁ := eq826
       have r₂ := eq27
       grind)
    | exact resolve eq826 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq832 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq830 eq20
    | exact resolve eq20 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq838 : y ≠ y ∨ y = (M.op y x) ∨ y = (k x y) := by
    first
    | exact superpose eq830 eq78
    | (have r₁ := eq78
       have r₂ := eq830
       grind)
    | exact resolve eq78 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq844 : y = (k x y) ∨ y = (M.op y x) := by grind
  clear eq838
  have eq850 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq832
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq832
    | exact resolve eq832 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq851 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq850 eq26
    | exact resolve eq26 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2040 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq844
       grind)
    | exact superpose eq844 eq44
    | exact resolve eq44 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq2047 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq850 eq2040
    | exact resolve eq2040 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040
  have eq2049 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2047
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2047
    | exact resolve eq2047 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2047
  have eq2050 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq850 eq2049
    | exact resolve eq2049 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2049
  have eq2053 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2050 eq96
    | (have j0 := eq96 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq96 eq2050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2050
  have eq2054 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by grind
  clear eq2053
  have eq2056 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq851 eq2054
    | exact resolve eq2054 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2054
  have eq2059 : y = (M.op y x) := by
    first
    | (have r₁ := eq2056
       have r₂ := eq27
       grind)
    | exact resolve eq2056 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2056
  have eq2069 : y ≠ y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq2059
       grind)
    | exact superpose eq2059 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2059
       grind)
    | exact resolve eq13 eq2059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059
  have eq2081 : (M.op x y) = (k x y) := by grind
  clear eq2069
  have eq2084 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq2081
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2081
    | exact resolve eq2081 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2081
  have eq2091 : y = (k x y) := by
    first
    | exact superpose eq830 eq2084
    | exact resolve eq2084 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830 eq2084
  have eq2186 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq2091
       grind)
    | exact superpose eq2091 eq44
    | exact resolve eq44 eq2091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq2091
  have eq2193 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq850 eq2186
    | exact resolve eq2186 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2186
  have eq2195 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2193
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2193
    | exact resolve eq2193 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2193
  have eq2196 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq850 eq2195
    | exact resolve eq2195 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850 eq2195
  have eq2305 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2196 eq96
    | (have j0 := eq96 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq96 eq2196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq2196
  have eq2306 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq2305
  have eq2308 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq851 eq2306
    | exact resolve eq2306 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851 eq2306
  have eq2311 : False := by grind
  exact eq2311
